%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXa9DIbJ7Z

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:38 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   69 (  96 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  613 ( 860 expanded)
%              Number of equality atoms :   60 (  87 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ C @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k1_enumset1 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X4 ) @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X0 @ X3 @ X2 ) @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','44'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X12 @ X11 @ X10 )
      = ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X9 @ X7 @ X8 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k1_enumset1 @ sk_B @ sk_C @ sk_A )
 != ( k1_enumset1 @ sk_B @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','45','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXa9DIbJ7Z
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.90/2.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.90/2.10  % Solved by: fo/fo7.sh
% 1.90/2.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.90/2.10  % done 2652 iterations in 1.641s
% 1.90/2.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.90/2.10  % SZS output start Refutation
% 1.90/2.10  thf(sk_B_type, type, sk_B: $i).
% 1.90/2.10  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.90/2.10  thf(sk_C_type, type, sk_C: $i).
% 1.90/2.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.90/2.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.90/2.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.90/2.10  thf(sk_A_type, type, sk_A: $i).
% 1.90/2.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.90/2.10  thf(t137_enumset1, conjecture,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.90/2.10       ( k1_enumset1 @ A @ B @ C ) ))).
% 1.90/2.10  thf(zf_stmt_0, negated_conjecture,
% 1.90/2.10    (~( ![A:$i,B:$i,C:$i]:
% 1.90/2.10        ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 1.90/2.10          ( k1_enumset1 @ A @ B @ C ) ) )),
% 1.90/2.10    inference('cnf.neg', [status(esa)], [t137_enumset1])).
% 1.90/2.10  thf('0', plain,
% 1.90/2.10      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.90/2.10         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 1.90/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.90/2.10  thf(t100_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ C @ A ) ))).
% 1.90/2.10  thf('1', plain,
% 1.90/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.90/2.10  thf('2', plain,
% 1.90/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.90/2.10  thf('3', plain,
% 1.90/2.10      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ sk_C @ sk_A))
% 1.90/2.10         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['0', '1', '2'])).
% 1.90/2.10  thf(l53_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i,D:$i]:
% 1.90/2.10     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.90/2.10       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.90/2.10  thf('4', plain,
% 1.90/2.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X3 @ X4 @ X5 @ X6)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X3 @ X4) @ (k2_tarski @ X5 @ X6)))),
% 1.90/2.10      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.90/2.10  thf('5', plain,
% 1.90/2.10      (((k2_enumset1 @ sk_B @ sk_A @ sk_C @ sk_A)
% 1.90/2.10         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['3', '4'])).
% 1.90/2.10  thf(t69_enumset1, axiom,
% 1.90/2.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.90/2.10  thf('6', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.10  thf('7', plain,
% 1.90/2.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X3 @ X4 @ X5 @ X6)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X3 @ X4) @ (k2_tarski @ X5 @ X6)))),
% 1.90/2.10      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.90/2.10  thf('8', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['6', '7'])).
% 1.90/2.10  thf(t71_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.90/2.10  thf('9', plain,
% 1.90/2.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.90/2.10           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.90/2.10      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.90/2.10  thf('10', plain,
% 1.90/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.90/2.10  thf(t70_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.90/2.10  thf('11', plain,
% 1.90/2.10      (![X17 : $i, X18 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.90/2.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.90/2.10  thf('12', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['10', '11'])).
% 1.90/2.10  thf('13', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X0 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['9', '12'])).
% 1.90/2.10  thf('14', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 1.90/2.10           = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['8', '13'])).
% 1.90/2.10  thf('15', plain,
% 1.90/2.10      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.10  thf(t43_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k1_enumset1 @ A @ B @ C ) =
% 1.90/2.10       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 1.90/2.10  thf('16', plain,
% 1.90/2.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X13 @ X14 @ X15)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X15)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t43_enumset1])).
% 1.90/2.10  thf('17', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X0 @ X0 @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['15', '16'])).
% 1.90/2.10  thf('18', plain,
% 1.90/2.10      (![X17 : $i, X18 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.90/2.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.90/2.10  thf('19', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_tarski @ X0 @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.90/2.10      inference('demod', [status(thm)], ['17', '18'])).
% 1.90/2.10  thf(t4_xboole_1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.90/2.10       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.90/2.10  thf('20', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 1.90/2.10           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.90/2.10  thf('21', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 1.90/2.10              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['19', '20'])).
% 1.90/2.10  thf('22', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X1))
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['14', '21'])).
% 1.90/2.10  thf('23', plain,
% 1.90/2.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X3 @ X4 @ X5 @ X6)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X3 @ X4) @ (k2_tarski @ X5 @ X6)))),
% 1.90/2.10      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.90/2.10  thf('24', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 1.90/2.10      inference('demod', [status(thm)], ['22', '23'])).
% 1.90/2.10  thf('25', plain,
% 1.90/2.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.90/2.10           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.90/2.10      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.90/2.10  thf('26', plain,
% 1.90/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.90/2.10  thf('27', plain,
% 1.90/2.10      (![X17 : $i, X18 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.90/2.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.90/2.10  thf('28', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['26', '27'])).
% 1.90/2.10  thf('29', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['25', '28'])).
% 1.90/2.10  thf('30', plain,
% 1.90/2.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X13 @ X14 @ X15)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X15)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t43_enumset1])).
% 1.90/2.10  thf('31', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X0 @ X1 @ X2)
% 1.90/2.10           = (k2_xboole_0 @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0) @ 
% 1.90/2.10              (k1_tarski @ X2)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['29', '30'])).
% 1.90/2.10  thf('32', plain,
% 1.90/2.10      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.10  thf('33', plain,
% 1.90/2.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X3 @ X4 @ X5 @ X6)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X3 @ X4) @ (k2_tarski @ X5 @ X6)))),
% 1.90/2.10      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.90/2.10  thf('34', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 1.90/2.10           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 1.90/2.10      inference('cnf', [status(esa)], [t4_xboole_1])).
% 1.90/2.10  thf('35', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 1.90/2.10           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 1.90/2.10              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['33', '34'])).
% 1.90/2.10  thf('36', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.90/2.10         ((k2_xboole_0 @ (k2_enumset1 @ X0 @ X0 @ X3 @ X2) @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 1.90/2.10              (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ X1)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['32', '35'])).
% 1.90/2.10  thf('37', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 1.90/2.10              (k2_xboole_0 @ (k2_tarski @ X2 @ X2) @ (k1_tarski @ X0))))),
% 1.90/2.10      inference('sup+', [status(thm)], ['31', '36'])).
% 1.90/2.10  thf('38', plain,
% 1.90/2.10      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.10  thf('39', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X1 @ X1 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.90/2.10      inference('sup+', [status(thm)], ['25', '28'])).
% 1.90/2.10  thf('40', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['6', '7'])).
% 1.90/2.10  thf('41', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_tarski @ X1 @ X0)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 1.90/2.10      inference('sup+', [status(thm)], ['39', '40'])).
% 1.90/2.10  thf('42', plain,
% 1.90/2.10      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.90/2.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.90/2.10  thf('43', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i]:
% 1.90/2.10         ((k2_tarski @ X1 @ X0)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 1.90/2.10      inference('demod', [status(thm)], ['41', '42'])).
% 1.90/2.10  thf('44', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X2 @ X1 @ X0)
% 1.90/2.10           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X2)))),
% 1.90/2.10      inference('demod', [status(thm)], ['37', '38', '43'])).
% 1.90/2.10  thf('45', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k2_enumset1 @ X2 @ X1 @ X0 @ X1) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 1.90/2.10      inference('demod', [status(thm)], ['24', '44'])).
% 1.90/2.10  thf(t102_enumset1, axiom,
% 1.90/2.10    (![A:$i,B:$i,C:$i]:
% 1.90/2.10     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 1.90/2.10  thf('46', plain,
% 1.90/2.10      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X12 @ X11 @ X10) = (k1_enumset1 @ X10 @ X11 @ X12))),
% 1.90/2.10      inference('cnf', [status(esa)], [t102_enumset1])).
% 1.90/2.10  thf('47', plain,
% 1.90/2.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X9 @ X7 @ X8) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 1.90/2.10      inference('cnf', [status(esa)], [t100_enumset1])).
% 1.90/2.10  thf('48', plain,
% 1.90/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.90/2.10         ((k1_enumset1 @ X2 @ X1 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 1.90/2.10      inference('sup+', [status(thm)], ['46', '47'])).
% 1.90/2.10  thf('49', plain,
% 1.90/2.10      (((k1_enumset1 @ sk_B @ sk_C @ sk_A)
% 1.90/2.10         != (k1_enumset1 @ sk_B @ sk_C @ sk_A))),
% 1.90/2.10      inference('demod', [status(thm)], ['5', '45', '48'])).
% 1.90/2.10  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 1.90/2.10  
% 1.90/2.10  % SZS output end Refutation
% 1.90/2.10  
% 1.90/2.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
