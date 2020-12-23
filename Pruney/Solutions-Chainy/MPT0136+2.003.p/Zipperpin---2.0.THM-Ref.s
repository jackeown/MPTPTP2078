%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BEpVDywlfo

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  81 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  440 ( 809 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t52_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
        = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X9 @ X10 @ X11 ) @ ( k1_enumset1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F )
 != ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BEpVDywlfo
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 33 iterations in 0.042s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.55  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.55  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.55  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.55  thf(t52_enumset1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.55        ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.55          ( k2_xboole_0 @
% 0.21/0.55            ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t52_enumset1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.21/0.55         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.21/0.55             (k2_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t41_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_tarski @ A @ B ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         ((k2_tarski @ X15 @ X16)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         ((k2_tarski @ X15 @ X16)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.55  thf(t4_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.55       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.21/0.55           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.55  thf(t43_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.21/0.55           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.21/0.55              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.55  thf(t46_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.55       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X20 @ X21 @ X22) @ (k1_tarski @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k1_tarski @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X6)
% 0.21/0.55           = (k2_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.21/0.55              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.21/0.55           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.55              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['18', '21'])).
% 0.21/0.55  thf(l62_enumset1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.55     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.55       ( k2_xboole_0 @
% 0.21/0.55         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.55         ((k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.55           = (k2_xboole_0 @ (k1_enumset1 @ X9 @ X10 @ X11) @ 
% 0.21/0.55              (k1_enumset1 @ X12 @ X13 @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.55         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.55           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.55              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (((k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)
% 0.21/0.55         != (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.55  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
