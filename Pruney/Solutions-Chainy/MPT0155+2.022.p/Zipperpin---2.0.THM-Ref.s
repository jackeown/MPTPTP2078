%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cybd2Dgqqx

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:29 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 117 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  572 (1187 expanded)
%              Number of equality atoms :   50 ( 106 expanded)
%              Maximal formula depth    :   15 (   8 average)

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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_enumset1 @ X43 @ X43 @ X44 )
      = ( k2_tarski @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_tarski @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X2 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cybd2Dgqqx
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 131 iterations in 0.091s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(t71_enumset1, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.37/0.56         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t70_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X43 : $i, X44 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 0.37/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.56  thf(t44_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf(t69_enumset1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.56  thf('4', plain, (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf('5', plain, (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf(t43_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X43 : $i, X44 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 0.37/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_tarski @ X0 @ X1)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_tarski @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['3', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.37/0.56              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf(t48_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.56     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ 
% 0.37/0.56              (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.56           = (k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf(t55_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.56       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.37/0.56           = (k2_xboole_0 @ (k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26) @ 
% 0.37/0.56              (k1_tarski @ X27)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.37/0.56              (k2_tarski @ X0 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.37/0.56              (k2_tarski @ X4 @ X4)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['18', '21'])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X43 : $i, X44 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X43 @ X43 @ X44) = (k2_tarski @ X43 @ X44))),
% 0.37/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.56  thf(l62_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.56       ( k2_xboole_0 @
% 0.37/0.56         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 0.37/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ 
% 0.37/0.56              (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.37/0.56              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ 
% 0.37/0.56              (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.37/0.56           = (k3_enumset1 @ X1 @ X0 @ X4 @ X3 @ X2))),
% 0.37/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.37/0.56              (k2_tarski @ X4 @ X4)))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['13', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.56           = (k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_tarski @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['4', '9'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X10 @ X11) @ (k1_tarski @ X12)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.37/0.56           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X1 @ X0 @ X2)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0) @ 
% 0.37/0.56              (k2_tarski @ X2 @ X2)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['32', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.37/0.56           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.37/0.56              (k2_tarski @ X4 @ X4)))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '27'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.37/0.56           = (k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.37/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.37/0.56         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '39'])).
% 0.37/0.56  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
