%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osUSrX62ZI

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:17 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 213 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  579 (1540 expanded)
%              Number of equality atoms :   70 ( 205 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['4','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','54','55'])).

thf('57',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.osUSrX62ZI
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:20:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 748 iterations in 0.292s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(t100_xboole_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i]:
% 0.53/0.74        ( ( k4_xboole_0 @ A @ B ) =
% 0.53/0.74          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.53/0.74         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(t47_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X9 : $i, X10 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.53/0.74           = (k4_xboole_0 @ X9 @ X10))),
% 0.53/0.74      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.74  thf(d6_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k5_xboole_0 @ A @ B ) =
% 0.53/0.74       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X1)
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.53/0.74              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['1', '2'])).
% 0.53/0.74  thf(t48_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X1)
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.74              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.53/0.74  thf(t41_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.74       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.53/0.74           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.53/0.74              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.53/0.74      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.74  thf(t1_boole, axiom,
% 0.53/0.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.74  thf('10', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.74  thf(t46_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (![X7 : $i, X8 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X7 @ (k2_xboole_0 @ X7 @ X8)) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.53/0.74  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf(t98_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.53/0.74           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.53/0.74  thf(t3_boole, axiom,
% 0.53/0.74    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.74  thf('15', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X1)
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.53/0.74           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.74  thf(t4_boole, axiom,
% 0.53/0.74    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t4_boole])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('20', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.74  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['19', '20'])).
% 0.53/0.74  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['14', '21'])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X1)
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['22', '23'])).
% 0.53/0.74  thf(t53_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.53/0.74       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.53/0.74           = (k3_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ 
% 0.53/0.74              (k4_xboole_0 @ X14 @ X16)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t53_xboole_1])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['24', '25'])).
% 0.53/0.74  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X1)
% 0.53/0.74           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X0 @ X0)
% 0.53/0.74           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.53/0.74  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('31', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.74  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.53/0.74  thf('33', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.53/0.74      inference('sup+', [status(thm)], ['32', '33'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ X0)
% 0.53/0.74           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['34', '35'])).
% 0.53/0.74  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['10', '11'])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 0.53/0.74      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '38'])).
% 0.53/0.74  thf('40', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['9', '39', '40'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 0.53/0.74           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X17 @ X18)
% 0.53/0.74           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.53/0.74           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.53/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.53/0.74           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['41', '44'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '38'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.53/0.74           = (k3_xboole_0 @ X11 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.53/0.74           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('sup+', [status(thm)], ['46', '47'])).
% 0.53/0.74  thf('49', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.53/0.74      inference('demod', [status(thm)], ['48', '49'])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['45', '50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.53/0.74      inference('sup+', [status(thm)], ['4', '51'])).
% 0.53/0.74  thf('53', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['26', '38'])).
% 0.53/0.74  thf('54', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['52', '53'])).
% 0.53/0.74  thf('55', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.53/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['3', '54', '55'])).
% 0.53/0.74  thf('57', plain,
% 0.53/0.74      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['0', '56'])).
% 0.53/0.74  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
