%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q3aj8k12mP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:19 EST 2020

% Result     : Theorem 44.49s
% Output     : Refutation 44.49s
% Verified   : 
% Statistics : Number of formulae       :  192 (1428 expanded)
%              Number of leaves         :   18 ( 486 expanded)
%              Depth                    :   26
%              Number of atoms          : 1619 (10217 expanded)
%              Number of equality atoms :  184 (1420 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['3','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['48','55','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','30'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['99','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['88','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('111',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','116','117','118'])).

thf('120',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['119','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('149',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('154',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['152','155'])).

thf('157',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['127','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('163',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('164',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','162','167','168','169'])).

thf('171',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','170'])).

thf('172',plain,(
    $false ),
    inference(simplify,[status(thm)],['171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q3aj8k12mP
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 44.49/44.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.49/44.75  % Solved by: fo/fo7.sh
% 44.49/44.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.49/44.75  % done 14672 iterations in 44.293s
% 44.49/44.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.49/44.75  % SZS output start Refutation
% 44.49/44.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.49/44.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.49/44.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.49/44.75  thf(sk_B_type, type, sk_B: $i).
% 44.49/44.75  thf(sk_A_type, type, sk_A: $i).
% 44.49/44.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.49/44.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 44.49/44.75  thf(t101_xboole_1, conjecture,
% 44.49/44.75    (![A:$i,B:$i]:
% 44.49/44.75     ( ( k5_xboole_0 @ A @ B ) =
% 44.49/44.75       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.49/44.75  thf(zf_stmt_0, negated_conjecture,
% 44.49/44.75    (~( ![A:$i,B:$i]:
% 44.49/44.75        ( ( k5_xboole_0 @ A @ B ) =
% 44.49/44.75          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 44.49/44.75    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 44.49/44.75  thf('0', plain,
% 44.49/44.75      (((k5_xboole_0 @ sk_A @ sk_B)
% 44.49/44.75         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 44.49/44.75             (k3_xboole_0 @ sk_A @ sk_B)))),
% 44.49/44.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.49/44.75  thf(commutativity_k3_xboole_0, axiom,
% 44.49/44.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 44.49/44.75  thf('1', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf(t100_xboole_1, axiom,
% 44.49/44.75    (![A:$i,B:$i]:
% 44.49/44.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.49/44.75  thf('2', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('3', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf(t91_xboole_1, axiom,
% 44.49/44.75    (![A:$i,B:$i,C:$i]:
% 44.49/44.75     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 44.49/44.75       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 44.49/44.75  thf('4', plain,
% 44.49/44.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 44.49/44.75           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.49/44.75  thf(t92_xboole_1, axiom,
% 44.49/44.75    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 44.49/44.75  thf('5', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('6', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 44.49/44.75           = (k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['4', '5'])).
% 44.49/44.75  thf('7', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('8', plain,
% 44.49/44.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 44.49/44.75           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.49/44.75  thf('9', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['7', '8'])).
% 44.49/44.75  thf(t2_boole, axiom,
% 44.49/44.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 44.49/44.75  thf('10', plain,
% 44.49/44.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t2_boole])).
% 44.49/44.75  thf('11', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('12', plain,
% 44.49/44.75      (![X0 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['10', '11'])).
% 44.49/44.75  thf(t5_boole, axiom,
% 44.49/44.75    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 44.49/44.75  thf('13', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['12', '13'])).
% 44.49/44.75  thf(t98_xboole_1, axiom,
% 44.49/44.75    (![A:$i,B:$i]:
% 44.49/44.75     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 44.49/44.75  thf('15', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('16', plain,
% 44.49/44.75      (![X0 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['14', '15'])).
% 44.49/44.75  thf('17', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf('18', plain,
% 44.49/44.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t2_boole])).
% 44.49/44.75  thf('19', plain,
% 44.49/44.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['17', '18'])).
% 44.49/44.75  thf('20', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('21', plain,
% 44.49/44.75      (![X0 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 44.49/44.75           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['19', '20'])).
% 44.49/44.75  thf('22', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('23', plain,
% 44.49/44.75      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['21', '22'])).
% 44.49/44.75  thf('24', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('25', plain,
% 44.49/44.75      (![X0 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['23', '24'])).
% 44.49/44.75  thf('26', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['25', '26'])).
% 44.49/44.75  thf(commutativity_k2_xboole_0, axiom,
% 44.49/44.75    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 44.49/44.75  thf('28', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.49/44.75  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['27', '28'])).
% 44.49/44.75  thf('30', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['16', '29'])).
% 44.49/44.75  thf('31', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['9', '30'])).
% 44.49/44.75  thf('32', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['6', '31'])).
% 44.49/44.75  thf('33', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('34', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['32', '33'])).
% 44.49/44.75  thf('35', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['3', '34'])).
% 44.49/44.75  thf('36', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['32', '33'])).
% 44.49/44.75  thf('37', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['9', '30'])).
% 44.49/44.75  thf('38', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['36', '37'])).
% 44.49/44.75  thf('39', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['35', '38'])).
% 44.49/44.75  thf('40', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('41', plain,
% 44.49/44.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 44.49/44.75           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.49/44.75  thf('42', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['40', '41'])).
% 44.49/44.75  thf('43', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['39', '42'])).
% 44.49/44.75  thf('44', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('45', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['9', '30'])).
% 44.49/44.75  thf('46', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X1 @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['44', '45'])).
% 44.49/44.75  thf('47', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['40', '41'])).
% 44.49/44.75  thf('48', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ 
% 44.49/44.75           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['46', '47'])).
% 44.49/44.75  thf('49', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf(t49_xboole_1, axiom,
% 44.49/44.75    (![A:$i,B:$i,C:$i]:
% 44.49/44.75     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 44.49/44.75       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 44.49/44.75  thf('50', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('51', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 44.49/44.75      inference('sup+', [status(thm)], ['49', '50'])).
% 44.49/44.75  thf('52', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('53', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 44.49/44.75           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['51', '52'])).
% 44.49/44.75  thf('54', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf('55', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 44.49/44.75           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['53', '54'])).
% 44.49/44.75  thf('56', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['25', '26'])).
% 44.49/44.75  thf(t21_xboole_1, axiom,
% 44.49/44.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 44.49/44.75  thf('58', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('59', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['57', '58'])).
% 44.49/44.75  thf('60', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('61', plain,
% 44.49/44.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['59', '60'])).
% 44.49/44.75  thf('62', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['61', '62'])).
% 44.49/44.75  thf('64', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('65', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('66', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['64', '65'])).
% 44.49/44.75  thf('67', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['63', '66'])).
% 44.49/44.75  thf('68', plain,
% 44.49/44.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t2_boole])).
% 44.49/44.75  thf('69', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('70', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 44.49/44.75  thf('71', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['56', '70'])).
% 44.49/44.75  thf('72', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.49/44.75  thf('73', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('74', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['72', '73'])).
% 44.49/44.75  thf('75', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('76', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['74', '75'])).
% 44.49/44.75  thf('77', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('78', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['76', '77'])).
% 44.49/44.75  thf('79', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['71', '78'])).
% 44.49/44.75  thf('80', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('81', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['79', '80'])).
% 44.49/44.75  thf('82', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf('83', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['81', '82'])).
% 44.49/44.75  thf('84', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('85', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k4_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['83', '84'])).
% 44.49/44.75  thf('86', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['64', '65'])).
% 44.49/44.75  thf('87', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['85', '86'])).
% 44.49/44.75  thf('88', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ 
% 44.49/44.75           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 44.49/44.75           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 44.49/44.75      inference('demod', [status(thm)], ['48', '55', '87'])).
% 44.49/44.75  thf('89', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['72', '73'])).
% 44.49/44.75  thf('90', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf('91', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['89', '90'])).
% 44.49/44.75  thf('92', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['36', '37'])).
% 44.49/44.75  thf('93', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['91', '92'])).
% 44.49/44.75  thf('94', plain,
% 44.49/44.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 44.49/44.75         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 44.49/44.75           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t91_xboole_1])).
% 44.49/44.75  thf('95', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('96', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ 
% 44.49/44.75              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['94', '95'])).
% 44.49/44.75  thf('97', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ 
% 44.49/44.75              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.49/44.75               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['93', '96'])).
% 44.49/44.75  thf('98', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['91', '92'])).
% 44.49/44.75  thf('99', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ 
% 44.49/44.75              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.49/44.75               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))))),
% 44.49/44.75      inference('demod', [status(thm)], ['97', '98'])).
% 44.49/44.75  thf('100', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.49/44.75  thf('101', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('102', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['9', '30'])).
% 44.49/44.75  thf('103', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['101', '102'])).
% 44.49/44.75  thf('104', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X1 @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['100', '103'])).
% 44.49/44.75  thf('105', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['91', '92'])).
% 44.49/44.75  thf('106', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k4_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['104', '105'])).
% 44.49/44.75  thf('107', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k4_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['104', '105'])).
% 44.49/44.75  thf('108', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ 
% 44.49/44.75              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.49/44.75               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 44.49/44.75      inference('demod', [status(thm)], ['99', '106', '107'])).
% 44.49/44.75  thf('109', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ 
% 44.49/44.75              (k2_xboole_0 @ X0 @ 
% 44.49/44.75               (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['88', '108'])).
% 44.49/44.75  thf('110', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['57', '58'])).
% 44.49/44.75  thf('111', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('112', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (k4_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['110', '111'])).
% 44.49/44.75  thf('113', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf('114', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 44.49/44.75           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['112', '113'])).
% 44.49/44.75  thf('115', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('116', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['114', '115'])).
% 44.49/44.75  thf('117', plain,
% 44.49/44.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t2_boole])).
% 44.49/44.75  thf('118', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['25', '26'])).
% 44.49/44.75  thf('119', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['109', '116', '117', '118'])).
% 44.49/44.75  thf('120', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('121', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf('122', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['120', '121'])).
% 44.49/44.75  thf('123', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['36', '37'])).
% 44.49/44.75  thf('124', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 44.49/44.75      inference('demod', [status(thm)], ['122', '123'])).
% 44.49/44.75  thf('125', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['101', '102'])).
% 44.49/44.75  thf('126', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X1 @ X0)
% 44.49/44.75           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['124', '125'])).
% 44.49/44.75  thf('127', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['119', '126'])).
% 44.49/44.75  thf('128', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 44.49/44.75  thf('129', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('demod', [status(thm)], ['91', '92'])).
% 44.49/44.75  thf('130', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 44.49/44.75           (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['128', '129'])).
% 44.49/44.75  thf('131', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 44.49/44.75  thf('132', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['36', '37'])).
% 44.49/44.75  thf('133', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['1', '2'])).
% 44.49/44.75  thf('134', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k4_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 44.49/44.75  thf('135', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['57', '58'])).
% 44.49/44.75  thf('136', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['64', '65'])).
% 44.49/44.75  thf('137', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['135', '136'])).
% 44.49/44.75  thf('138', plain,
% 44.49/44.75      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.49/44.75  thf('139', plain,
% 44.49/44.75      (![X17 : $i, X18 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X17 @ X18)
% 44.49/44.75           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t98_xboole_1])).
% 44.49/44.75  thf('140', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 44.49/44.75           = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['137', '138', '139'])).
% 44.49/44.75  thf('141', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (k4_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['110', '111'])).
% 44.49/44.75  thf('142', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['140', '141'])).
% 44.49/44.75  thf('143', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['134', '142'])).
% 44.49/44.75  thf('144', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.49/44.75  thf('145', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.49/44.75  thf('146', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['67', '68', '69'])).
% 44.49/44.75  thf('147', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (X1))),
% 44.49/44.75      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 44.49/44.75  thf('148', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['79', '80'])).
% 44.49/44.75  thf('149', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('150', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['148', '149'])).
% 44.49/44.75  thf('151', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 44.49/44.75      inference('cnf', [status(esa)], [t5_boole])).
% 44.49/44.75  thf('152', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['150', '151'])).
% 44.49/44.75  thf('153', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('154', plain,
% 44.49/44.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 44.49/44.75      inference('cnf', [status(esa)], [t49_xboole_1])).
% 44.49/44.75  thf('155', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1))
% 44.49/44.75           = (k4_xboole_0 @ X0 @ X1))),
% 44.49/44.75      inference('sup+', [status(thm)], ['153', '154'])).
% 44.49/44.75  thf('156', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['152', '155'])).
% 44.49/44.75  thf('157', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('158', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((X1)
% 44.49/44.75           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('demod', [status(thm)], ['156', '157'])).
% 44.49/44.75  thf('159', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ X1)
% 44.49/44.75           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0)))),
% 44.49/44.75      inference('sup+', [status(thm)], ['147', '158'])).
% 44.49/44.75  thf('160', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X1 @ X0)
% 44.49/44.75           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 44.49/44.75      inference('demod', [status(thm)], ['127', '159'])).
% 44.49/44.75  thf('161', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 44.49/44.75              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 44.49/44.75      inference('sup+', [status(thm)], ['43', '160'])).
% 44.49/44.75  thf('162', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 44.49/44.75           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 44.49/44.75      inference('sup+', [status(thm)], ['49', '50'])).
% 44.49/44.75  thf('163', plain,
% 44.49/44.75      (![X6 : $i, X7 : $i]:
% 44.49/44.75         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 44.49/44.75      inference('cnf', [status(esa)], [t21_xboole_1])).
% 44.49/44.75  thf('164', plain,
% 44.49/44.75      (![X4 : $i, X5 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X4 @ X5)
% 44.49/44.75           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 44.49/44.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 44.49/44.75  thf('165', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 44.49/44.75           = (k5_xboole_0 @ X0 @ X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['163', '164'])).
% 44.49/44.75  thf('166', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t92_xboole_1])).
% 44.49/44.75  thf('167', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 44.49/44.75      inference('demod', [status(thm)], ['165', '166'])).
% 44.49/44.75  thf('168', plain,
% 44.49/44.75      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 44.49/44.75      inference('cnf', [status(esa)], [t2_boole])).
% 44.49/44.75  thf('169', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.49/44.75      inference('sup+', [status(thm)], ['12', '13'])).
% 44.49/44.75  thf('170', plain,
% 44.49/44.75      (![X0 : $i, X1 : $i]:
% 44.49/44.75         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 44.49/44.75           = (k5_xboole_0 @ X1 @ X0))),
% 44.49/44.75      inference('demod', [status(thm)], ['161', '162', '167', '168', '169'])).
% 44.49/44.75  thf('171', plain,
% 44.49/44.75      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 44.49/44.75      inference('demod', [status(thm)], ['0', '170'])).
% 44.49/44.75  thf('172', plain, ($false), inference('simplify', [status(thm)], ['171'])).
% 44.49/44.75  
% 44.49/44.75  % SZS output end Refutation
% 44.49/44.75  
% 44.49/44.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
