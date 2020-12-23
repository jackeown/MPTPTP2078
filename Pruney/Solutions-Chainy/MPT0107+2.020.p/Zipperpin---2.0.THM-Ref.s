%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uQYt8KuOCI

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:12 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 285 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :  996 (2158 expanded)
%              Number of equality atoms :  125 ( 285 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20','25','26'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('67',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('68',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X6 = X5 )
      | ( ( k4_xboole_0 @ X6 @ X5 )
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
       != ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( X1
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
       != ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('76',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','80','87','88'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('90',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('94',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','99'])).

thf('101',plain,(
    $false ),
    inference(simplify,[status(thm)],['100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uQYt8KuOCI
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 1.32/1.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.32/1.51  % Solved by: fo/fo7.sh
% 1.32/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.51  % done 1318 iterations in 1.050s
% 1.32/1.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.32/1.51  % SZS output start Refutation
% 1.32/1.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.32/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.32/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.32/1.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.32/1.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.32/1.51  thf(t100_xboole_1, conjecture,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.32/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.51    (~( ![A:$i,B:$i]:
% 1.32/1.51        ( ( k4_xboole_0 @ A @ B ) =
% 1.32/1.51          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.32/1.51    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 1.32/1.51  thf('0', plain,
% 1.32/1.51      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.32/1.51         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.32/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.51  thf(commutativity_k3_xboole_0, axiom,
% 1.32/1.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.32/1.51  thf('1', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('2', plain,
% 1.32/1.51      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.32/1.51         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.32/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.32/1.51  thf(t47_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.32/1.51  thf('3', plain,
% 1.32/1.51      (![X13 : $i, X14 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 1.32/1.51           = (k4_xboole_0 @ X13 @ X14))),
% 1.32/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.32/1.51  thf(t3_boole, axiom,
% 1.32/1.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.32/1.51  thf('4', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.32/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.32/1.51  thf(t48_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.32/1.51  thf('5', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('6', plain,
% 1.32/1.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['4', '5'])).
% 1.32/1.51  thf(t2_boole, axiom,
% 1.32/1.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.32/1.51  thf('7', plain,
% 1.32/1.51      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.51      inference('cnf', [status(esa)], [t2_boole])).
% 1.32/1.51  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['6', '7'])).
% 1.32/1.51  thf(t49_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i,C:$i]:
% 1.32/1.51     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.32/1.51       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.32/1.51  thf('9', plain,
% 1.32/1.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.32/1.51           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.32/1.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.32/1.51  thf('10', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.32/1.51           = (k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['8', '9'])).
% 1.32/1.51  thf('11', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('12', plain,
% 1.32/1.51      (![X13 : $i, X14 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 1.32/1.51           = (k4_xboole_0 @ X13 @ X14))),
% 1.32/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.32/1.51  thf('13', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['11', '12'])).
% 1.32/1.51  thf('14', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['10', '13'])).
% 1.32/1.51  thf('15', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['3', '14'])).
% 1.32/1.51  thf('16', plain,
% 1.32/1.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.32/1.51           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.32/1.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.32/1.51  thf(t98_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.32/1.51  thf('17', plain,
% 1.32/1.51      (![X28 : $i, X29 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X28 @ X29)
% 1.32/1.51           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.32/1.51  thf('18', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.32/1.51      inference('sup+', [status(thm)], ['16', '17'])).
% 1.32/1.51  thf('19', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['15', '18'])).
% 1.32/1.51  thf('20', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('21', plain,
% 1.32/1.51      (![X13 : $i, X14 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 1.32/1.51           = (k4_xboole_0 @ X13 @ X14))),
% 1.32/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.32/1.51  thf('22', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('23', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['21', '22'])).
% 1.32/1.51  thf('24', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('25', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k3_xboole_0 @ X1 @ X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['23', '24'])).
% 1.32/1.51  thf(t5_boole, axiom,
% 1.32/1.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.32/1.51  thf('26', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.32/1.51      inference('cnf', [status(esa)], [t5_boole])).
% 1.32/1.51  thf('27', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['19', '20', '25', '26'])).
% 1.32/1.51  thf(t40_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.32/1.51  thf('28', plain,
% 1.32/1.51      (![X8 : $i, X9 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 1.32/1.51           = (k4_xboole_0 @ X8 @ X9))),
% 1.32/1.51      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.32/1.51  thf('29', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('30', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['28', '29'])).
% 1.32/1.51  thf('31', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('32', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['30', '31'])).
% 1.32/1.51  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['6', '7'])).
% 1.32/1.51  thf(t53_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i,C:$i]:
% 1.32/1.51     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.32/1.51       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.32/1.51  thf('34', plain,
% 1.32/1.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 1.32/1.51           = (k3_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 1.32/1.51              (k4_xboole_0 @ X20 @ X22)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t53_xboole_1])).
% 1.32/1.51  thf('35', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['33', '34'])).
% 1.32/1.51  thf('36', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('37', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.32/1.51  thf('38', plain,
% 1.32/1.51      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.51      inference('cnf', [status(esa)], [t2_boole])).
% 1.32/1.51  thf('39', plain,
% 1.32/1.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['37', '38'])).
% 1.32/1.51  thf('40', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['35', '36', '39'])).
% 1.32/1.51  thf('41', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('42', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.32/1.51           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['40', '41'])).
% 1.32/1.51  thf('43', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.32/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.32/1.51  thf('44', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['42', '43'])).
% 1.32/1.51  thf('45', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['32', '44'])).
% 1.32/1.51  thf('46', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.32/1.51           = (k3_xboole_0 @ X1 @ X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['27', '45'])).
% 1.32/1.51  thf('47', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['11', '12'])).
% 1.32/1.51  thf('48', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.32/1.51           = (k3_xboole_0 @ X1 @ X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['46', '47'])).
% 1.32/1.51  thf('49', plain,
% 1.32/1.51      (![X28 : $i, X29 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X28 @ X29)
% 1.32/1.51           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.32/1.51  thf('50', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.32/1.51           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['48', '49'])).
% 1.32/1.51  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['6', '7'])).
% 1.32/1.51  thf('52', plain,
% 1.32/1.51      (![X15 : $i, X16 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.32/1.51           = (k3_xboole_0 @ X15 @ X16))),
% 1.32/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.32/1.51  thf('53', plain,
% 1.32/1.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['51', '52'])).
% 1.32/1.51  thf('54', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.32/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.32/1.51  thf('55', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.32/1.51  thf('56', plain,
% 1.32/1.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.32/1.51           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.32/1.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.32/1.51  thf('57', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.32/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['55', '56'])).
% 1.32/1.51  thf('58', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.32/1.51      inference('sup+', [status(thm)], ['16', '17'])).
% 1.32/1.51  thf('59', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['57', '58'])).
% 1.32/1.51  thf('60', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.32/1.51  thf('61', plain,
% 1.32/1.51      (![X8 : $i, X9 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 1.32/1.51           = (k4_xboole_0 @ X8 @ X9))),
% 1.32/1.51      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.32/1.51  thf('62', plain,
% 1.32/1.51      (![X28 : $i, X29 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X28 @ X29)
% 1.32/1.51           = (k5_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.32/1.51  thf('63', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['61', '62'])).
% 1.32/1.51  thf('64', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ X1)
% 1.32/1.51           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['59', '60', '63'])).
% 1.32/1.51  thf('65', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['35', '36', '39'])).
% 1.32/1.51  thf('66', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['35', '36', '39'])).
% 1.32/1.51  thf('67', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.32/1.51  thf('68', plain,
% 1.32/1.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.32/1.51           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.32/1.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.32/1.51  thf(t32_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i]:
% 1.32/1.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 1.32/1.51       ( ( A ) = ( B ) ) ))).
% 1.32/1.51  thf('69', plain,
% 1.32/1.51      (![X5 : $i, X6 : $i]:
% 1.32/1.51         (((X6) = (X5)) | ((k4_xboole_0 @ X6 @ X5) != (k4_xboole_0 @ X5 @ X6)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t32_xboole_1])).
% 1.32/1.51  thf('70', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.51         (((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.32/1.51            != (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.32/1.51          | ((X0) = (k3_xboole_0 @ X2 @ X1)))),
% 1.32/1.51      inference('sup-', [status(thm)], ['68', '69'])).
% 1.32/1.51  thf('71', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         (((k4_xboole_0 @ X1 @ X0)
% 1.32/1.51            != (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 1.32/1.51          | ((X1) = (k3_xboole_0 @ X0 @ X0)))),
% 1.32/1.51      inference('sup-', [status(thm)], ['67', '70'])).
% 1.32/1.51  thf('72', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['53', '54'])).
% 1.32/1.51  thf('73', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         (((k4_xboole_0 @ X1 @ X0)
% 1.32/1.51            != (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 1.32/1.51          | ((X1) = (X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['71', '72'])).
% 1.32/1.51  thf('74', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.32/1.51            != (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.32/1.51          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.32/1.51      inference('sup-', [status(thm)], ['66', '73'])).
% 1.32/1.51  thf('75', plain,
% 1.32/1.51      (![X8 : $i, X9 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 1.32/1.51           = (k4_xboole_0 @ X8 @ X9))),
% 1.32/1.51      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.32/1.51  thf('76', plain,
% 1.32/1.51      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.32/1.51      inference('cnf', [status(esa)], [t2_boole])).
% 1.32/1.51  thf('77', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         (((k4_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.32/1.51          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.32/1.51  thf('78', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         (((k1_xboole_0) != (k1_xboole_0))
% 1.32/1.51          | ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.32/1.51              = (k2_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup-', [status(thm)], ['65', '77'])).
% 1.32/1.51  thf('79', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.32/1.51           = (k2_xboole_0 @ X1 @ X0))),
% 1.32/1.51      inference('simplify', [status(thm)], ['78'])).
% 1.32/1.51  thf('80', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['64', '79'])).
% 1.32/1.51  thf('81', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.32/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['55', '56'])).
% 1.32/1.51  thf('82', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.32/1.51      inference('demod', [status(thm)], ['10', '13'])).
% 1.32/1.51  thf('83', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.32/1.51      inference('sup+', [status(thm)], ['16', '17'])).
% 1.32/1.51  thf('84', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.32/1.51           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['82', '83'])).
% 1.32/1.51  thf('85', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.32/1.51      inference('cnf', [status(esa)], [t5_boole])).
% 1.32/1.51  thf('86', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 1.32/1.51      inference('demod', [status(thm)], ['84', '85'])).
% 1.32/1.51  thf('87', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 1.32/1.51      inference('sup+', [status(thm)], ['81', '86'])).
% 1.32/1.51  thf(commutativity_k5_xboole_0, axiom,
% 1.32/1.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.32/1.51  thf('88', plain,
% 1.32/1.51      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.32/1.51  thf('89', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((X0)
% 1.32/1.51           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.32/1.51      inference('demod', [status(thm)], ['50', '80', '87', '88'])).
% 1.32/1.51  thf(t92_xboole_1, axiom,
% 1.32/1.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.32/1.51  thf('90', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 1.32/1.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.32/1.51  thf(t91_xboole_1, axiom,
% 1.32/1.51    (![A:$i,B:$i,C:$i]:
% 1.32/1.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.32/1.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.32/1.51  thf('91', plain,
% 1.32/1.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.32/1.51         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 1.32/1.51           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 1.32/1.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.32/1.51  thf('92', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.32/1.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('sup+', [status(thm)], ['90', '91'])).
% 1.32/1.51  thf('93', plain,
% 1.32/1.51      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.32/1.51  thf('94', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 1.32/1.51      inference('cnf', [status(esa)], [t5_boole])).
% 1.32/1.51  thf('95', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['93', '94'])).
% 1.32/1.51  thf('96', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['92', '95'])).
% 1.32/1.51  thf('97', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ X1)
% 1.32/1.51           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.32/1.51      inference('sup+', [status(thm)], ['89', '96'])).
% 1.32/1.51  thf('98', plain,
% 1.32/1.51      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.32/1.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.32/1.51  thf('99', plain,
% 1.32/1.51      (![X0 : $i, X1 : $i]:
% 1.32/1.51         ((k4_xboole_0 @ X0 @ X1)
% 1.32/1.51           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.32/1.51      inference('demod', [status(thm)], ['97', '98'])).
% 1.32/1.51  thf('100', plain,
% 1.32/1.51      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.32/1.51      inference('demod', [status(thm)], ['2', '99'])).
% 1.32/1.51  thf('101', plain, ($false), inference('simplify', [status(thm)], ['100'])).
% 1.32/1.51  
% 1.32/1.51  % SZS output end Refutation
% 1.32/1.51  
% 1.32/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
