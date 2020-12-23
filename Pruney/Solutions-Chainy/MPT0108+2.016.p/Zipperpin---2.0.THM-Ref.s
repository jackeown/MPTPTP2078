%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TJiUuCJ0hv

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:19 EST 2020

% Result     : Theorem 22.51s
% Output     : Refutation 22.51s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 143 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   22
%              Number of atoms          :  542 (1024 expanded)
%              Number of equality atoms :   67 ( 135 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t101_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t101_xboole_1])).

thf('0',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','52'])).

thf('54',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TJiUuCJ0hv
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:08:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.51/22.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.51/22.72  % Solved by: fo/fo7.sh
% 22.51/22.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.51/22.72  % done 7766 iterations in 22.291s
% 22.51/22.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.51/22.72  % SZS output start Refutation
% 22.51/22.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 22.51/22.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 22.51/22.72  thf(sk_B_type, type, sk_B: $i).
% 22.51/22.72  thf(sk_A_type, type, sk_A: $i).
% 22.51/22.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 22.51/22.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 22.51/22.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.51/22.72  thf(t101_xboole_1, conjecture,
% 22.51/22.72    (![A:$i,B:$i]:
% 22.51/22.72     ( ( k5_xboole_0 @ A @ B ) =
% 22.51/22.72       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 22.51/22.72  thf(zf_stmt_0, negated_conjecture,
% 22.51/22.72    (~( ![A:$i,B:$i]:
% 22.51/22.72        ( ( k5_xboole_0 @ A @ B ) =
% 22.51/22.72          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 22.51/22.72    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 22.51/22.72  thf('0', plain,
% 22.51/22.72      (((k5_xboole_0 @ sk_A @ sk_B)
% 22.51/22.72         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 22.51/22.72             (k3_xboole_0 @ sk_A @ sk_B)))),
% 22.51/22.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.51/22.72  thf(commutativity_k3_xboole_0, axiom,
% 22.51/22.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 22.51/22.72  thf('1', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.51/22.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.51/22.72  thf(t100_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i]:
% 22.51/22.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 22.51/22.72  thf('2', plain,
% 22.51/22.72      (![X5 : $i, X6 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X5 @ X6)
% 22.51/22.72           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.51/22.72  thf(commutativity_k5_xboole_0, axiom,
% 22.51/22.72    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 22.51/22.72  thf('3', plain,
% 22.51/22.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 22.51/22.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 22.51/22.72  thf(idempotence_k2_xboole_0, axiom,
% 22.51/22.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 22.51/22.72  thf('4', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 22.51/22.72      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 22.51/22.72  thf(t46_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i]:
% 22.51/22.72     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 22.51/22.72  thf('5', plain,
% 22.51/22.72      (![X13 : $i, X14 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 22.51/22.72      inference('cnf', [status(esa)], [t46_xboole_1])).
% 22.51/22.72  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['4', '5'])).
% 22.51/22.72  thf(t48_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i]:
% 22.51/22.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 22.51/22.72  thf('7', plain,
% 22.51/22.72      (![X15 : $i, X16 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 22.51/22.72           = (k3_xboole_0 @ X15 @ X16))),
% 22.51/22.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.51/22.72  thf('8', plain,
% 22.51/22.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['6', '7'])).
% 22.51/22.72  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['4', '5'])).
% 22.51/22.72  thf(t98_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i]:
% 22.51/22.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 22.51/22.72  thf('10', plain,
% 22.51/22.72      (![X23 : $i, X24 : $i]:
% 22.51/22.72         ((k2_xboole_0 @ X23 @ X24)
% 22.51/22.72           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 22.51/22.72  thf('11', plain,
% 22.51/22.72      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['9', '10'])).
% 22.51/22.72  thf('12', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 22.51/22.72      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 22.51/22.72  thf('13', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 22.51/22.72      inference('demod', [status(thm)], ['11', '12'])).
% 22.51/22.72  thf('14', plain,
% 22.51/22.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 22.51/22.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 22.51/22.72  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['13', '14'])).
% 22.51/22.72  thf('16', plain,
% 22.51/22.72      (![X5 : $i, X6 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X5 @ X6)
% 22.51/22.72           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.51/22.72  thf('17', plain,
% 22.51/22.72      (![X0 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['15', '16'])).
% 22.51/22.72  thf('18', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 22.51/22.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 22.51/22.72  thf('19', plain,
% 22.51/22.72      (![X5 : $i, X6 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X5 @ X6)
% 22.51/22.72           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 22.51/22.72  thf('20', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ X1)
% 22.51/22.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['18', '19'])).
% 22.51/22.72  thf('21', plain,
% 22.51/22.72      (![X0 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 22.51/22.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['17', '20'])).
% 22.51/22.72  thf('22', plain,
% 22.51/22.72      (![X23 : $i, X24 : $i]:
% 22.51/22.72         ((k2_xboole_0 @ X23 @ X24)
% 22.51/22.72           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 22.51/22.72  thf('23', plain,
% 22.51/22.72      (![X0 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 22.51/22.72      inference('demod', [status(thm)], ['21', '22'])).
% 22.51/22.72  thf(t1_boole, axiom,
% 22.51/22.72    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 22.51/22.72  thf('24', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 22.51/22.72      inference('cnf', [status(esa)], [t1_boole])).
% 22.51/22.72  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 22.51/22.72      inference('demod', [status(thm)], ['23', '24'])).
% 22.51/22.72  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 22.51/22.72      inference('demod', [status(thm)], ['8', '25'])).
% 22.51/22.72  thf('27', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ X1)
% 22.51/22.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['18', '19'])).
% 22.51/22.72  thf('28', plain,
% 22.51/22.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['26', '27'])).
% 22.51/22.72  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['4', '5'])).
% 22.51/22.72  thf('30', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 22.51/22.72      inference('demod', [status(thm)], ['28', '29'])).
% 22.51/22.72  thf(t91_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i,C:$i]:
% 22.51/22.72     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 22.51/22.72       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 22.51/22.72  thf('31', plain,
% 22.51/22.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 22.51/22.72         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 22.51/22.72           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 22.51/22.72  thf('32', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 22.51/22.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['30', '31'])).
% 22.51/22.72  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['13', '14'])).
% 22.51/22.72  thf('34', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('demod', [status(thm)], ['32', '33'])).
% 22.51/22.72  thf('35', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['3', '34'])).
% 22.51/22.72  thf('36', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((X1)
% 22.51/22.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['2', '35'])).
% 22.51/22.72  thf('37', plain,
% 22.51/22.72      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 22.51/22.72      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 22.51/22.72  thf('38', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((X1)
% 22.51/22.72           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('demod', [status(thm)], ['36', '37'])).
% 22.51/22.72  thf('39', plain,
% 22.51/22.72      (![X23 : $i, X24 : $i]:
% 22.51/22.72         ((k2_xboole_0 @ X23 @ X24)
% 22.51/22.72           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 22.51/22.72  thf('40', plain,
% 22.51/22.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 22.51/22.72         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 22.51/22.72           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 22.51/22.72  thf('41', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.51/22.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 22.51/22.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['39', '40'])).
% 22.51/22.72  thf('42', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 22.51/22.72           = (k5_xboole_0 @ X1 @ X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['38', '41'])).
% 22.51/22.72  thf('43', plain,
% 22.51/22.72      (![X13 : $i, X14 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 22.51/22.72      inference('cnf', [status(esa)], [t46_xboole_1])).
% 22.51/22.72  thf('44', plain,
% 22.51/22.72      (![X15 : $i, X16 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 22.51/22.72           = (k3_xboole_0 @ X15 @ X16))),
% 22.51/22.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 22.51/22.72  thf('45', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 22.51/22.72           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['43', '44'])).
% 22.51/22.72  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 22.51/22.72      inference('demod', [status(thm)], ['23', '24'])).
% 22.51/22.72  thf('47', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('demod', [status(thm)], ['45', '46'])).
% 22.51/22.72  thf(t16_xboole_1, axiom,
% 22.51/22.72    (![A:$i,B:$i,C:$i]:
% 22.51/22.72     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 22.51/22.72       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 22.51/22.72  thf('48', plain,
% 22.51/22.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 22.51/22.72         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 22.51/22.72           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 22.51/22.72      inference('cnf', [status(esa)], [t16_xboole_1])).
% 22.51/22.72  thf('49', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ X1)
% 22.51/22.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['18', '19'])).
% 22.51/22.72  thf('50', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 22.51/22.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 22.51/22.72      inference('sup+', [status(thm)], ['48', '49'])).
% 22.51/22.72  thf('51', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0))
% 22.51/22.72           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X2 @ X0)))),
% 22.51/22.72      inference('sup+', [status(thm)], ['47', '50'])).
% 22.51/22.72  thf('52', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 22.51/22.72           = (k5_xboole_0 @ X1 @ X0))),
% 22.51/22.72      inference('demod', [status(thm)], ['42', '51'])).
% 22.51/22.72  thf('53', plain,
% 22.51/22.72      (![X0 : $i, X1 : $i]:
% 22.51/22.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 22.51/22.72           = (k5_xboole_0 @ X1 @ X0))),
% 22.51/22.72      inference('sup+', [status(thm)], ['1', '52'])).
% 22.51/22.72  thf('54', plain,
% 22.51/22.72      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 22.51/22.72      inference('demod', [status(thm)], ['0', '53'])).
% 22.51/22.72  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 22.51/22.72  
% 22.51/22.72  % SZS output end Refutation
% 22.51/22.72  
% 22.51/22.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
