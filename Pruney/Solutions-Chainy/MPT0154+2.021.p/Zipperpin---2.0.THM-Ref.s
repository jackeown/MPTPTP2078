%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YwB7A5THvE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:24 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 485 expanded)
%              Number of leaves         :   24 ( 169 expanded)
%              Depth                    :   22
%              Number of atoms          :  530 (3281 expanded)
%              Number of equality atoms :   68 ( 471 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','28'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','28'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','28'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YwB7A5THvE
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:16:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 602 iterations in 0.465s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.95  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.77/0.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.95  thf(t70_enumset1, conjecture,
% 0.77/0.95    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.77/0.95  thf('0', plain,
% 0.77/0.95      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t41_enumset1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( k2_tarski @ A @ B ) =
% 0.77/0.95       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.77/0.95  thf('1', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i]:
% 0.77/0.95         ((k2_tarski @ X22 @ X23)
% 0.77/0.95           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.77/0.95  thf(t7_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.95  thf('2', plain,
% 0.77/0.95      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.77/0.95      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.95  thf(t28_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (![X6 : $i, X7 : $i]:
% 0.77/0.95         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.77/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.95  thf('4', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.95  thf('5', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.95  thf(t100_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.77/0.95  thf('6', plain,
% 0.77/0.95      (![X3 : $i, X4 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X3 @ X4)
% 0.77/0.95           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X0 @ X1)
% 0.77/0.95           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['5', '6'])).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.77/0.95           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['4', '7'])).
% 0.77/0.95  thf(idempotence_k3_xboole_0, axiom,
% 0.77/0.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.95  thf('9', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.95      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.77/0.95  thf('10', plain,
% 0.77/0.95      (![X3 : $i, X4 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X3 @ X4)
% 0.77/0.95           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.95  thf('11', plain,
% 0.77/0.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/0.95  thf(t48_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.95  thf('12', plain,
% 0.77/0.95      (![X8 : $i, X9 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.77/0.95           = (k3_xboole_0 @ X8 @ X9))),
% 0.77/0.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.95  thf(t4_boole, axiom,
% 0.77/0.95    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.77/0.95      inference('cnf', [status(esa)], [t4_boole])).
% 0.77/0.95  thf('14', plain,
% 0.77/0.95      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['12', '13'])).
% 0.77/0.95  thf('15', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.95      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (![X3 : $i, X4 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X3 @ X4)
% 0.77/0.95           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.77/0.95  thf('18', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/0.95  thf('19', plain,
% 0.77/0.95      (![X10 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.77/0.95      inference('cnf', [status(esa)], [t4_boole])).
% 0.77/0.95  thf(t98_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      (![X16 : $i, X17 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ X16 @ X17)
% 0.77/0.95           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.77/0.95  thf('21', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['19', '20'])).
% 0.77/0.95  thf(t1_boole, axiom,
% 0.77/0.95    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.77/0.95  thf('22', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.77/0.95      inference('cnf', [status(esa)], [t1_boole])).
% 0.77/0.95  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['18', '23'])).
% 0.77/0.95  thf('25', plain,
% 0.77/0.95      (![X8 : $i, X9 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.77/0.95           = (k3_xboole_0 @ X8 @ X9))),
% 0.77/0.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.95  thf('26', plain,
% 0.77/0.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['24', '25'])).
% 0.77/0.95  thf('27', plain,
% 0.77/0.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.77/0.95  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/0.95      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.95  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['11', '28'])).
% 0.77/0.95  thf(t91_xboole_1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.95       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.77/0.95  thf('30', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.77/0.95           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.95  thf('31', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k1_xboole_0)
% 0.77/0.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['29', '30'])).
% 0.77/0.95  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['11', '28'])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.77/0.95           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.77/0.95  thf('34', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['32', '33'])).
% 0.77/0.95  thf('35', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['11', '28'])).
% 0.77/0.95  thf('36', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['32', '33'])).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['35', '36'])).
% 0.77/0.95  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('39', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('demod', [status(thm)], ['34', '39'])).
% 0.77/0.95  thf('41', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 0.77/0.95           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['31', '40'])).
% 0.77/0.95  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.95  thf('43', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.95      inference('demod', [status(thm)], ['41', '42'])).
% 0.77/0.95  thf('44', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('demod', [status(thm)], ['34', '39'])).
% 0.77/0.95  thf('45', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['43', '44'])).
% 0.77/0.95  thf('46', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.77/0.95           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('demod', [status(thm)], ['8', '45'])).
% 0.77/0.95  thf('47', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.77/0.95      inference('demod', [status(thm)], ['34', '39'])).
% 0.77/0.95  thf('48', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.95           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['46', '47'])).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      (![X16 : $i, X17 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ X16 @ X17)
% 0.77/0.95           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.77/0.95  thf('50', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ X0 @ X1)
% 0.77/0.95           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.77/0.95      inference('demod', [status(thm)], ['48', '49'])).
% 0.77/0.95  thf('51', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.77/0.95           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['1', '50'])).
% 0.77/0.95  thf('52', plain,
% 0.77/0.95      (![X22 : $i, X23 : $i]:
% 0.77/0.95         ((k2_tarski @ X22 @ X23)
% 0.77/0.95           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.77/0.95  thf(t42_enumset1, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.77/0.95       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.77/0.95  thf('53', plain,
% 0.77/0.95      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.77/0.95         ((k1_enumset1 @ X24 @ X25 @ X26)
% 0.77/0.95           = (k2_xboole_0 @ (k1_tarski @ X24) @ (k2_tarski @ X25 @ X26)))),
% 0.77/0.95      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.77/0.95  thf('54', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.77/0.95      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.77/0.95  thf('55', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.77/0.95      inference('demod', [status(thm)], ['0', '54'])).
% 0.77/0.95  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
