%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O7mq6lJIUm

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:23 EST 2020

% Result     : Theorem 47.19s
% Output     : Refutation 47.19s
% Verified   : 
% Statistics : Number of formulae       :  125 (4318 expanded)
%              Number of leaves         :   18 (1481 expanded)
%              Depth                    :   23
%              Number of atoms          :  984 (31811 expanded)
%              Number of equality atoms :  117 (4310 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','54','55','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('63',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','30'])).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('94',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92','95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O7mq6lJIUm
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 47.19/47.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.19/47.41  % Solved by: fo/fo7.sh
% 47.19/47.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.19/47.41  % done 13227 iterations in 46.950s
% 47.19/47.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.19/47.41  % SZS output start Refutation
% 47.19/47.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 47.19/47.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.19/47.41  thf(sk_B_type, type, sk_B: $i).
% 47.19/47.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 47.19/47.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 47.19/47.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 47.19/47.41  thf(sk_A_type, type, sk_A: $i).
% 47.19/47.41  thf(t101_xboole_1, conjecture,
% 47.19/47.41    (![A:$i,B:$i]:
% 47.19/47.41     ( ( k5_xboole_0 @ A @ B ) =
% 47.19/47.41       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 47.19/47.41  thf(zf_stmt_0, negated_conjecture,
% 47.19/47.41    (~( ![A:$i,B:$i]:
% 47.19/47.41        ( ( k5_xboole_0 @ A @ B ) =
% 47.19/47.41          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 47.19/47.41    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 47.19/47.41  thf('0', plain,
% 47.19/47.41      (((k5_xboole_0 @ sk_A @ sk_B)
% 47.19/47.41         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 47.19/47.41             (k3_xboole_0 @ sk_A @ sk_B)))),
% 47.19/47.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.19/47.41  thf(t3_boole, axiom,
% 47.19/47.41    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 47.19/47.41  thf('1', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 47.19/47.41      inference('cnf', [status(esa)], [t3_boole])).
% 47.19/47.41  thf(t48_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i]:
% 47.19/47.41     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 47.19/47.41  thf('2', plain,
% 47.19/47.41      (![X15 : $i, X16 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 47.19/47.41           = (k3_xboole_0 @ X15 @ X16))),
% 47.19/47.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.19/47.41  thf('3', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['1', '2'])).
% 47.19/47.41  thf(t47_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i]:
% 47.19/47.41     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 47.19/47.41  thf('4', plain,
% 47.19/47.41      (![X13 : $i, X14 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 47.19/47.41           = (k4_xboole_0 @ X13 @ X14))),
% 47.19/47.41      inference('cnf', [status(esa)], [t47_xboole_1])).
% 47.19/47.41  thf('5', plain,
% 47.19/47.41      (![X0 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 47.19/47.41           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['3', '4'])).
% 47.19/47.41  thf('6', plain,
% 47.19/47.41      (![X15 : $i, X16 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 47.19/47.41           = (k3_xboole_0 @ X15 @ X16))),
% 47.19/47.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.19/47.41  thf('7', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 47.19/47.41      inference('cnf', [status(esa)], [t3_boole])).
% 47.19/47.41  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['5', '6', '7'])).
% 47.19/47.41  thf(t23_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i,C:$i]:
% 47.19/47.41     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 47.19/47.41       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 47.19/47.41  thf('9', plain,
% 47.19/47.41      (![X9 : $i, X10 : $i, X11 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 47.19/47.41           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t23_xboole_1])).
% 47.19/47.41  thf('10', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['8', '9'])).
% 47.19/47.41  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['5', '6', '7'])).
% 47.19/47.41  thf('12', plain,
% 47.19/47.41      (![X9 : $i, X10 : $i, X11 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 47.19/47.41           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t23_xboole_1])).
% 47.19/47.41  thf('13', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 47.19/47.41           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['11', '12'])).
% 47.19/47.41  thf(t98_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i]:
% 47.19/47.41     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 47.19/47.41  thf('14', plain,
% 47.19/47.41      (![X26 : $i, X27 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X26 @ X27)
% 47.19/47.41           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.19/47.41  thf('15', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['1', '2'])).
% 47.19/47.41  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['5', '6', '7'])).
% 47.19/47.41  thf(t100_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i]:
% 47.19/47.41     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 47.19/47.41  thf('17', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('18', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['16', '17'])).
% 47.19/47.41  thf('19', plain,
% 47.19/47.41      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['15', '18'])).
% 47.19/47.41  thf('20', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('21', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 47.19/47.41      inference('cnf', [status(esa)], [t3_boole])).
% 47.19/47.41  thf('22', plain,
% 47.19/47.41      (![X26 : $i, X27 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X26 @ X27)
% 47.19/47.41           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.19/47.41  thf('23', plain,
% 47.19/47.41      (![X0 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['21', '22'])).
% 47.19/47.41  thf('24', plain,
% 47.19/47.41      (![X0 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 47.19/47.41           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['20', '23'])).
% 47.19/47.41  thf(t22_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 47.19/47.41  thf('25', plain,
% 47.19/47.41      (![X7 : $i, X8 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 47.19/47.41      inference('cnf', [status(esa)], [t22_xboole_1])).
% 47.19/47.41  thf('26', plain,
% 47.19/47.41      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['24', '25'])).
% 47.19/47.41  thf('27', plain,
% 47.19/47.41      (![X15 : $i, X16 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 47.19/47.41           = (k3_xboole_0 @ X15 @ X16))),
% 47.19/47.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.19/47.41  thf('28', plain,
% 47.19/47.41      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['26', '27'])).
% 47.19/47.41  thf(commutativity_k3_xboole_0, axiom,
% 47.19/47.41    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 47.19/47.41  thf('29', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.19/47.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.19/47.41  thf('30', plain,
% 47.19/47.41      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['28', '29'])).
% 47.19/47.41  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['19', '30'])).
% 47.19/47.41  thf('32', plain,
% 47.19/47.41      (![X0 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['21', '22'])).
% 47.19/47.41  thf('33', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 47.19/47.41           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 47.19/47.41      inference('sup+', [status(thm)], ['31', '32'])).
% 47.19/47.41  thf(t91_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i,C:$i]:
% 47.19/47.41     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 47.19/47.41       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 47.19/47.41  thf('34', plain,
% 47.19/47.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 47.19/47.41           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.19/47.41  thf('35', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['33', '34'])).
% 47.19/47.41  thf('36', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ k1_xboole_0 @ X1)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['33', '34'])).
% 47.19/47.41  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['19', '30'])).
% 47.19/47.41  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['19', '30'])).
% 47.19/47.41  thf('39', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['1', '2'])).
% 47.19/47.41  thf('40', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('41', plain,
% 47.19/47.41      (![X0 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['39', '40'])).
% 47.19/47.41  thf('42', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 47.19/47.41      inference('cnf', [status(esa)], [t3_boole])).
% 47.19/47.41  thf('43', plain,
% 47.19/47.41      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 47.19/47.41      inference('demod', [status(thm)], ['41', '42'])).
% 47.19/47.41  thf('44', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['16', '17'])).
% 47.19/47.41  thf('45', plain,
% 47.19/47.41      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 47.19/47.41      inference('demod', [status(thm)], ['43', '44'])).
% 47.19/47.41  thf('46', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['38', '45'])).
% 47.19/47.41  thf('47', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['37', '46'])).
% 47.19/47.41  thf('48', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['36', '47'])).
% 47.19/47.41  thf('49', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['35', '48'])).
% 47.19/47.41  thf('50', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X0 @ X1)
% 47.19/47.41           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['14', '49'])).
% 47.19/47.41  thf('51', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 47.19/47.41           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 47.19/47.41      inference('sup+', [status(thm)], ['13', '50'])).
% 47.19/47.41  thf('52', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.19/47.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.19/47.41  thf(t49_xboole_1, axiom,
% 47.19/47.41    (![A:$i,B:$i,C:$i]:
% 47.19/47.41     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 47.19/47.41       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 47.19/47.41  thf('53', plain,
% 47.19/47.41      (![X17 : $i, X18 : $i, X19 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 47.19/47.41           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 47.19/47.41      inference('cnf', [status(esa)], [t49_xboole_1])).
% 47.19/47.41  thf('54', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 47.19/47.41           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 47.19/47.41      inference('sup+', [status(thm)], ['52', '53'])).
% 47.19/47.41  thf('55', plain,
% 47.19/47.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['16', '17'])).
% 47.19/47.41  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['19', '30'])).
% 47.19/47.41  thf('57', plain,
% 47.19/47.41      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['28', '29'])).
% 47.19/47.41  thf('58', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['56', '57'])).
% 47.19/47.41  thf('59', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('60', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.19/47.41      inference('demod', [status(thm)], ['51', '54', '55', '58', '59'])).
% 47.19/47.41  thf('61', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k1_xboole_0)
% 47.19/47.41           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 47.19/47.41              (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 47.19/47.41      inference('sup+', [status(thm)], ['10', '60'])).
% 47.19/47.41  thf('62', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 47.19/47.41           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 47.19/47.41      inference('sup+', [status(thm)], ['52', '53'])).
% 47.19/47.41  thf('63', plain,
% 47.19/47.41      (![X13 : $i, X14 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 47.19/47.41           = (k4_xboole_0 @ X13 @ X14))),
% 47.19/47.41      inference('cnf', [status(esa)], [t47_xboole_1])).
% 47.19/47.41  thf('64', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k1_xboole_0)
% 47.19/47.41           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 47.19/47.41      inference('demod', [status(thm)], ['61', '62', '63'])).
% 47.19/47.41  thf('65', plain,
% 47.19/47.41      (![X17 : $i, X18 : $i, X19 : $i]:
% 47.19/47.41         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 47.19/47.41           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 47.19/47.41      inference('cnf', [status(esa)], [t49_xboole_1])).
% 47.19/47.41  thf('66', plain,
% 47.19/47.41      (![X26 : $i, X27 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X26 @ X27)
% 47.19/47.41           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.19/47.41  thf('67', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 47.19/47.41      inference('sup+', [status(thm)], ['65', '66'])).
% 47.19/47.41  thf('68', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['64', '67'])).
% 47.19/47.41  thf('69', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['38', '45'])).
% 47.19/47.41  thf('70', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k2_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['68', '69'])).
% 47.19/47.41  thf('71', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.19/47.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.19/47.41  thf('72', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('73', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X0 @ X1)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['71', '72'])).
% 47.19/47.41  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.19/47.41      inference('demod', [status(thm)], ['19', '30'])).
% 47.19/47.41  thf('75', plain,
% 47.19/47.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 47.19/47.41           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.19/47.41  thf('76', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k1_xboole_0)
% 47.19/47.41           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 47.19/47.41      inference('sup+', [status(thm)], ['74', '75'])).
% 47.19/47.41  thf('77', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['35', '48'])).
% 47.19/47.41  thf('78', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['76', '77'])).
% 47.19/47.41  thf('79', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['38', '45'])).
% 47.19/47.41  thf('80', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.19/47.41      inference('demod', [status(thm)], ['78', '79'])).
% 47.19/47.41  thf('81', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (X1))),
% 47.19/47.41      inference('sup+', [status(thm)], ['73', '80'])).
% 47.19/47.41  thf('82', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.19/47.41      inference('demod', [status(thm)], ['78', '79'])).
% 47.19/47.41  thf('83', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['35', '48'])).
% 47.19/47.41  thf('84', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['82', '83'])).
% 47.19/47.41  thf('85', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 47.19/47.41           = (X1))),
% 47.19/47.41      inference('demod', [status(thm)], ['81', '84'])).
% 47.19/47.41  thf('86', plain,
% 47.19/47.41      (![X26 : $i, X27 : $i]:
% 47.19/47.41         ((k2_xboole_0 @ X26 @ X27)
% 47.19/47.41           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.19/47.41  thf('87', plain,
% 47.19/47.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 47.19/47.41           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.19/47.41  thf('88', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 47.19/47.41           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['86', '87'])).
% 47.19/47.41  thf('89', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['85', '88'])).
% 47.19/47.41  thf('90', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.19/47.41      inference('demod', [status(thm)], ['78', '79'])).
% 47.19/47.41  thf('91', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k2_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['89', '90'])).
% 47.19/47.41  thf('92', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['82', '83'])).
% 47.19/47.41  thf('93', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['82', '83'])).
% 47.19/47.41  thf('94', plain,
% 47.19/47.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 47.19/47.41           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.19/47.41  thf('95', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['93', '94'])).
% 47.19/47.41  thf('96', plain,
% 47.19/47.41      (![X2 : $i, X3 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X2 @ X3)
% 47.19/47.41           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 47.19/47.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.19/47.41  thf('97', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k2_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['91', '92', '95', '96'])).
% 47.19/47.41  thf('98', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 47.19/47.41      inference('demod', [status(thm)], ['35', '48'])).
% 47.19/47.41  thf('99', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ X1 @ X0)
% 47.19/47.41           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['97', '98'])).
% 47.19/47.41  thf('100', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 47.19/47.41      inference('sup+', [status(thm)], ['70', '99'])).
% 47.19/47.41  thf('101', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['82', '83'])).
% 47.19/47.41  thf('102', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('sup+', [status(thm)], ['85', '88'])).
% 47.19/47.41  thf('103', plain,
% 47.19/47.41      (![X0 : $i, X1 : $i]:
% 47.19/47.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.19/47.41           = (k5_xboole_0 @ X1 @ X0))),
% 47.19/47.41      inference('demod', [status(thm)], ['100', '101', '102'])).
% 47.19/47.41  thf('104', plain,
% 47.19/47.41      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 47.19/47.41      inference('demod', [status(thm)], ['0', '103'])).
% 47.19/47.41  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 47.19/47.41  
% 47.19/47.41  % SZS output end Refutation
% 47.19/47.41  
% 47.19/47.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
