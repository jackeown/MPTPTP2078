%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRDd2vUwXn

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:10 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 271 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          :  561 (1956 expanded)
%              Number of equality atoms :   68 ( 263 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k4_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16','47','48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','53','54','55'])).

thf('57',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRDd2vUwXn
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.50/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.68  % Solved by: fo/fo7.sh
% 1.50/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.68  % done 1985 iterations in 1.220s
% 1.50/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.68  % SZS output start Refutation
% 1.50/1.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.50/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.50/1.68  thf(t100_xboole_1, conjecture,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.50/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.68    (~( ![A:$i,B:$i]:
% 1.50/1.68        ( ( k4_xboole_0 @ A @ B ) =
% 1.50/1.68          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.50/1.68    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 1.50/1.68  thf('0', plain,
% 1.50/1.68      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.50/1.68         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.50/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.68  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.68  thf('1', plain,
% 1.50/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.68  thf('2', plain,
% 1.50/1.68      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.50/1.68         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.50/1.68      inference('demod', [status(thm)], ['0', '1'])).
% 1.50/1.68  thf('3', plain,
% 1.50/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.68  thf(t47_xboole_1, axiom,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.50/1.68  thf('4', plain,
% 1.50/1.68      (![X18 : $i, X19 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.50/1.68           = (k4_xboole_0 @ X18 @ X19))),
% 1.50/1.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.50/1.68  thf('5', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k4_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('sup+', [status(thm)], ['3', '4'])).
% 1.50/1.68  thf(d6_xboole_0, axiom,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k5_xboole_0 @ A @ B ) =
% 1.50/1.68       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.50/1.68  thf('6', plain,
% 1.50/1.68      (![X10 : $i, X11 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ X10 @ X11)
% 1.50/1.68           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 1.50/1.68              (k4_xboole_0 @ X11 @ X10)))),
% 1.50/1.68      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.50/1.68  thf('7', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.68           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.50/1.68              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 1.50/1.68      inference('sup+', [status(thm)], ['5', '6'])).
% 1.50/1.68  thf('8', plain,
% 1.50/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.68  thf('9', plain,
% 1.50/1.68      (![X18 : $i, X19 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.50/1.68           = (k4_xboole_0 @ X18 @ X19))),
% 1.50/1.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.50/1.68  thf(t48_xboole_1, axiom,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.50/1.68  thf('10', plain,
% 1.50/1.68      (![X20 : $i, X21 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.50/1.68           = (k3_xboole_0 @ X20 @ X21))),
% 1.50/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.68  thf('11', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.50/1.68      inference('sup+', [status(thm)], ['9', '10'])).
% 1.50/1.68  thf('12', plain,
% 1.50/1.68      (![X20 : $i, X21 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.50/1.68           = (k3_xboole_0 @ X20 @ X21))),
% 1.50/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.68  thf('13', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k3_xboole_0 @ X1 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['11', '12'])).
% 1.50/1.68  thf('14', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.68           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.50/1.68              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 1.50/1.68      inference('sup+', [status(thm)], ['5', '6'])).
% 1.50/1.68  thf('15', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.50/1.68           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.50/1.68           = (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ 
% 1.50/1.68              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 1.50/1.68      inference('sup+', [status(thm)], ['13', '14'])).
% 1.50/1.68  thf('16', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k3_xboole_0 @ X1 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['11', '12'])).
% 1.50/1.68  thf(commutativity_k2_xboole_0, axiom,
% 1.50/1.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.50/1.68  thf('17', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.50/1.68  thf(t1_boole, axiom,
% 1.50/1.68    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.50/1.68  thf('18', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.50/1.68      inference('cnf', [status(esa)], [t1_boole])).
% 1.50/1.68  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.68  thf(t39_xboole_1, axiom,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.50/1.68  thf('20', plain,
% 1.50/1.68      (![X13 : $i, X14 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.50/1.68           = (k2_xboole_0 @ X13 @ X14))),
% 1.50/1.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.50/1.68  thf('21', plain,
% 1.50/1.68      (![X0 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['19', '20'])).
% 1.50/1.68  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.68  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.50/1.68      inference('demod', [status(thm)], ['21', '22'])).
% 1.50/1.68  thf('24', plain,
% 1.50/1.68      (![X20 : $i, X21 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.50/1.68           = (k3_xboole_0 @ X20 @ X21))),
% 1.50/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.68  thf('25', plain,
% 1.50/1.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['23', '24'])).
% 1.50/1.68  thf('26', plain,
% 1.50/1.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['23', '24'])).
% 1.50/1.68  thf(t51_xboole_1, axiom,
% 1.50/1.68    (![A:$i,B:$i]:
% 1.50/1.68     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.50/1.68       ( A ) ))).
% 1.50/1.68  thf('27', plain,
% 1.50/1.68      (![X22 : $i, X23 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.50/1.68           = (X22))),
% 1.50/1.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.50/1.68  thf('28', plain,
% 1.50/1.68      (![X0 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 1.50/1.68           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['26', '27'])).
% 1.50/1.68  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.50/1.68      inference('demod', [status(thm)], ['21', '22'])).
% 1.50/1.68  thf('30', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.50/1.68  thf('31', plain,
% 1.50/1.68      (![X13 : $i, X14 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.50/1.68           = (k2_xboole_0 @ X13 @ X14))),
% 1.50/1.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.50/1.68  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.50/1.68      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 1.50/1.68  thf('33', plain,
% 1.50/1.68      (![X10 : $i, X11 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ X10 @ X11)
% 1.50/1.68           = (k2_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ 
% 1.50/1.68              (k4_xboole_0 @ X11 @ X10)))),
% 1.50/1.68      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.50/1.68  thf('34', plain,
% 1.50/1.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['32', '33'])).
% 1.50/1.68  thf('35', plain,
% 1.50/1.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.68      inference('demod', [status(thm)], ['25', '34'])).
% 1.50/1.68  thf('36', plain,
% 1.50/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.68  thf('37', plain,
% 1.50/1.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['35', '36'])).
% 1.50/1.68  thf('38', plain,
% 1.50/1.68      (![X18 : $i, X19 : $i]:
% 1.50/1.68         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.50/1.68           = (k4_xboole_0 @ X18 @ X19))),
% 1.50/1.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.50/1.68  thf('39', plain,
% 1.50/1.68      (![X13 : $i, X14 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.50/1.68           = (k2_xboole_0 @ X13 @ X14))),
% 1.50/1.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.50/1.68  thf('40', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.50/1.68      inference('sup+', [status(thm)], ['38', '39'])).
% 1.50/1.68  thf('41', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.50/1.68  thf('42', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.50/1.68           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.50/1.68      inference('demod', [status(thm)], ['40', '41'])).
% 1.50/1.68  thf('43', plain,
% 1.50/1.68      (![X22 : $i, X23 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k4_xboole_0 @ X22 @ X23))
% 1.50/1.68           = (X22))),
% 1.50/1.68      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.50/1.68  thf('44', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 1.50/1.68      inference('sup+', [status(thm)], ['42', '43'])).
% 1.50/1.68  thf('45', plain,
% 1.50/1.68      (![X0 : $i]:
% 1.50/1.68         ((k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['37', '44'])).
% 1.50/1.68  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.68  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.68      inference('demod', [status(thm)], ['45', '46'])).
% 1.50/1.68  thf('48', plain,
% 1.50/1.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['32', '33'])).
% 1.50/1.68  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.68      inference('demod', [status(thm)], ['45', '46'])).
% 1.50/1.68  thf('50', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.50/1.68  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.68  thf('52', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.50/1.68      inference('demod', [status(thm)],
% 1.50/1.68                ['15', '16', '47', '48', '49', '50', '51'])).
% 1.50/1.68  thf('53', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['8', '52'])).
% 1.50/1.68  thf('54', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.50/1.68  thf('55', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.50/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.50/1.68  thf('56', plain,
% 1.50/1.68      (![X0 : $i, X1 : $i]:
% 1.50/1.68         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.50/1.68           = (k4_xboole_0 @ X1 @ X0))),
% 1.50/1.68      inference('demod', [status(thm)], ['7', '53', '54', '55'])).
% 1.50/1.68  thf('57', plain,
% 1.50/1.68      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.50/1.68      inference('demod', [status(thm)], ['2', '56'])).
% 1.50/1.68  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 1.50/1.68  
% 1.50/1.68  % SZS output end Refutation
% 1.50/1.68  
% 1.50/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
