%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MUwswP3yxA

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:00 EST 2020

% Result     : Theorem 3.62s
% Output     : Refutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 126 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  580 ( 983 expanded)
%              Number of equality atoms :   67 ( 118 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9','24','25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','23'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ X2 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MUwswP3yxA
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.62/3.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.62/3.81  % Solved by: fo/fo7.sh
% 3.62/3.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.62/3.81  % done 4134 iterations in 3.363s
% 3.62/3.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.62/3.81  % SZS output start Refutation
% 3.62/3.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.62/3.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.62/3.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.62/3.81  thf(sk_A_type, type, sk_A: $i).
% 3.62/3.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.62/3.81  thf(sk_B_type, type, sk_B: $i).
% 3.62/3.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.62/3.81  thf(t95_xboole_1, conjecture,
% 3.62/3.81    (![A:$i,B:$i]:
% 3.62/3.81     ( ( k3_xboole_0 @ A @ B ) =
% 3.62/3.81       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 3.62/3.81  thf(zf_stmt_0, negated_conjecture,
% 3.62/3.81    (~( ![A:$i,B:$i]:
% 3.62/3.81        ( ( k3_xboole_0 @ A @ B ) =
% 3.62/3.81          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 3.62/3.81    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 3.62/3.81  thf('0', plain,
% 3.62/3.81      (((k3_xboole_0 @ sk_A @ sk_B)
% 3.62/3.81         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 3.62/3.81             (k2_xboole_0 @ sk_A @ sk_B)))),
% 3.62/3.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.62/3.81  thf(commutativity_k3_xboole_0, axiom,
% 3.62/3.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.62/3.81  thf('1', plain,
% 3.62/3.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.62/3.81  thf(l98_xboole_1, axiom,
% 3.62/3.81    (![A:$i,B:$i]:
% 3.62/3.81     ( ( k5_xboole_0 @ A @ B ) =
% 3.62/3.81       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.62/3.81  thf('2', plain,
% 3.62/3.81      (![X6 : $i, X7 : $i]:
% 3.62/3.81         ((k5_xboole_0 @ X6 @ X7)
% 3.62/3.81           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 3.62/3.81      inference('cnf', [status(esa)], [l98_xboole_1])).
% 3.62/3.81  thf('3', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k5_xboole_0 @ X0 @ X1)
% 3.62/3.81           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['1', '2'])).
% 3.62/3.81  thf(t48_xboole_1, axiom,
% 3.62/3.81    (![A:$i,B:$i]:
% 3.62/3.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.62/3.81  thf('4', plain,
% 3.62/3.81      (![X13 : $i, X14 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.62/3.81           = (k3_xboole_0 @ X13 @ X14))),
% 3.62/3.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.62/3.81  thf(d6_xboole_0, axiom,
% 3.62/3.81    (![A:$i,B:$i]:
% 3.62/3.81     ( ( k5_xboole_0 @ A @ B ) =
% 3.62/3.81       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 3.62/3.81  thf('5', plain,
% 3.62/3.81      (![X4 : $i, X5 : $i]:
% 3.62/3.81         ((k5_xboole_0 @ X4 @ X5)
% 3.62/3.81           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 3.62/3.81      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.62/3.81  thf(commutativity_k2_xboole_0, axiom,
% 3.62/3.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.62/3.81  thf('6', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.62/3.81  thf('7', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 3.62/3.81           = (k5_xboole_0 @ X1 @ X0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['5', '6'])).
% 3.62/3.81  thf('8', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 3.62/3.81           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 3.62/3.81           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 3.62/3.81      inference('sup+', [status(thm)], ['4', '7'])).
% 3.62/3.81  thf(t41_xboole_1, axiom,
% 3.62/3.81    (![A:$i,B:$i,C:$i]:
% 3.62/3.81     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.62/3.81       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.62/3.81  thf('9', plain,
% 3.62/3.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.62/3.81           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.62/3.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.62/3.81  thf('10', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.62/3.81  thf(t3_boole, axiom,
% 3.62/3.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.62/3.81  thf('11', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.62/3.81      inference('cnf', [status(esa)], [t3_boole])).
% 3.62/3.81  thf('12', plain,
% 3.62/3.81      (![X13 : $i, X14 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.62/3.81           = (k3_xboole_0 @ X13 @ X14))),
% 3.62/3.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.62/3.81  thf('13', plain,
% 3.62/3.81      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['11', '12'])).
% 3.62/3.81  thf('14', plain,
% 3.62/3.81      (![X13 : $i, X14 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.62/3.81           = (k3_xboole_0 @ X13 @ X14))),
% 3.62/3.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.62/3.81  thf(t4_boole, axiom,
% 3.62/3.81    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 3.62/3.81  thf('15', plain,
% 3.62/3.81      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 3.62/3.81      inference('cnf', [status(esa)], [t4_boole])).
% 3.62/3.81  thf('16', plain,
% 3.62/3.81      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['14', '15'])).
% 3.62/3.81  thf('17', plain,
% 3.62/3.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.62/3.81  thf('18', plain,
% 3.62/3.81      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['16', '17'])).
% 3.62/3.81  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.62/3.81      inference('demod', [status(thm)], ['13', '18'])).
% 3.62/3.81  thf('20', plain,
% 3.62/3.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.62/3.81           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.62/3.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.62/3.81  thf('21', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.62/3.81           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['19', '20'])).
% 3.62/3.81  thf('22', plain,
% 3.62/3.81      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 3.62/3.81      inference('cnf', [status(esa)], [t4_boole])).
% 3.62/3.81  thf('23', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['21', '22'])).
% 3.62/3.81  thf('24', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['10', '23'])).
% 3.62/3.81  thf('25', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.62/3.81  thf('26', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.62/3.81  thf(t1_boole, axiom,
% 3.62/3.81    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.62/3.81  thf('27', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.62/3.81      inference('cnf', [status(esa)], [t1_boole])).
% 3.62/3.81  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['26', '27'])).
% 3.62/3.81  thf('29', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.62/3.81           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 3.62/3.81      inference('demod', [status(thm)], ['8', '9', '24', '25', '28'])).
% 3.62/3.81  thf('30', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 3.62/3.81           = (k5_xboole_0 @ X1 @ X0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['5', '6'])).
% 3.62/3.81  thf('31', plain,
% 3.62/3.81      (![X4 : $i, X5 : $i]:
% 3.62/3.81         ((k5_xboole_0 @ X4 @ X5)
% 3.62/3.81           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 3.62/3.81      inference('cnf', [status(esa)], [d6_xboole_0])).
% 3.62/3.81  thf('32', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['30', '31'])).
% 3.62/3.81  thf('33', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ X1 @ X0)
% 3.62/3.81           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['29', '32'])).
% 3.62/3.81  thf('34', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 3.62/3.81           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['3', '33'])).
% 3.62/3.81  thf('35', plain,
% 3.62/3.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.62/3.81  thf('36', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 3.62/3.81      inference('sup+', [status(thm)], ['30', '31'])).
% 3.62/3.81  thf('37', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 3.62/3.81           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['34', '35', '36'])).
% 3.62/3.81  thf('38', plain,
% 3.62/3.81      (![X13 : $i, X14 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.62/3.81           = (k3_xboole_0 @ X13 @ X14))),
% 3.62/3.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.62/3.81  thf('39', plain,
% 3.62/3.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.62/3.81           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.62/3.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.62/3.81  thf('40', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 3.62/3.81           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['38', '39'])).
% 3.62/3.81  thf('41', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.62/3.81  thf('42', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['10', '23'])).
% 3.62/3.81  thf('43', plain,
% 3.62/3.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.62/3.81           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.62/3.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.62/3.81  thf('44', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.62/3.81           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['42', '43'])).
% 3.62/3.81  thf('45', plain,
% 3.62/3.81      (![X15 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 3.62/3.81      inference('cnf', [status(esa)], [t4_boole])).
% 3.62/3.81  thf('46', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k1_xboole_0)
% 3.62/3.81           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['44', '45'])).
% 3.62/3.81  thf('47', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k1_xboole_0)
% 3.62/3.81           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.62/3.81      inference('sup+', [status(thm)], ['41', '46'])).
% 3.62/3.81  thf('48', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k1_xboole_0)
% 3.62/3.81           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['40', '47'])).
% 3.62/3.81  thf('49', plain,
% 3.62/3.81      (![X13 : $i, X14 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 3.62/3.81           = (k3_xboole_0 @ X13 @ X14))),
% 3.62/3.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.62/3.81  thf('50', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ k1_xboole_0)
% 3.62/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('sup+', [status(thm)], ['48', '49'])).
% 3.62/3.81  thf('51', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 3.62/3.81      inference('cnf', [status(esa)], [t3_boole])).
% 3.62/3.81  thf('52', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ X0 @ X2)
% 3.62/3.81           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['50', '51'])).
% 3.62/3.81  thf('53', plain,
% 3.62/3.81      (![X0 : $i, X1 : $i]:
% 3.62/3.81         ((k3_xboole_0 @ X0 @ X1)
% 3.62/3.81           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 3.62/3.81      inference('demod', [status(thm)], ['37', '52'])).
% 3.62/3.81  thf('54', plain,
% 3.62/3.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 3.62/3.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.62/3.81  thf('55', plain,
% 3.62/3.81      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 3.62/3.81      inference('demod', [status(thm)], ['0', '53', '54'])).
% 3.62/3.81  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 3.62/3.81  
% 3.62/3.81  % SZS output end Refutation
% 3.62/3.81  
% 3.64/3.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
