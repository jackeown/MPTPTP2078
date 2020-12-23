%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iF1skcmXkG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:23 EST 2020

% Result     : Theorem 23.62s
% Output     : Refutation 23.62s
% Verified   : 
% Statistics : Number of formulae       :  232 (47992 expanded)
%              Number of leaves         :   18 (16255 expanded)
%              Depth                    :   44
%              Number of atoms          : 1975 (383831 expanded)
%              Number of equality atoms :  224 (47984 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','51'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','54','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('69',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','54','57'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','54','57'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['91','98','99'])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['86','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','54','57'])).

thf('124',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122','127'])).

thf('129',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('135',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('139',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('140',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['138','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('147',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['137','149'])).

thf('151',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['133','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('155',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('156',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('159',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('168',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['153','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['121','122','127'])).

thf('173',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['178','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('185',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['184','187'])).

thf('189',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['183','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k5_xboole_0 @ X12 @ ( k5_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['192','199','200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['202','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['178','181','182'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','210'])).

thf('212',plain,(
    $false ),
    inference(simplify,[status(thm)],['211'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iF1skcmXkG
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 23.62/23.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 23.62/23.84  % Solved by: fo/fo7.sh
% 23.62/23.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.62/23.84  % done 9893 iterations in 23.389s
% 23.62/23.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 23.62/23.84  % SZS output start Refutation
% 23.62/23.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 23.62/23.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.62/23.84  thf(sk_B_type, type, sk_B: $i).
% 23.62/23.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 23.62/23.84  thf(sk_A_type, type, sk_A: $i).
% 23.62/23.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 23.62/23.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 23.62/23.84  thf(t101_xboole_1, conjecture,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k5_xboole_0 @ A @ B ) =
% 23.62/23.84       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 23.62/23.84  thf(zf_stmt_0, negated_conjecture,
% 23.62/23.84    (~( ![A:$i,B:$i]:
% 23.62/23.84        ( ( k5_xboole_0 @ A @ B ) =
% 23.62/23.84          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 23.62/23.84    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 23.62/23.84  thf('0', plain,
% 23.62/23.84      (((k5_xboole_0 @ sk_A @ sk_B)
% 23.62/23.84         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 23.62/23.84             (k3_xboole_0 @ sk_A @ sk_B)))),
% 23.62/23.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.62/23.84  thf(t93_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k2_xboole_0 @ A @ B ) =
% 23.62/23.84       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 23.62/23.84  thf('1', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf(t98_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 23.62/23.84  thf('2', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('3', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf(t92_xboole_1, axiom,
% 23.62/23.84    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 23.62/23.84  thf('4', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 23.62/23.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 23.62/23.84  thf(t91_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i,C:$i]:
% 23.62/23.84     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 23.62/23.84       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 23.62/23.84  thf('5', plain,
% 23.62/23.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 23.62/23.84           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t91_xboole_1])).
% 23.62/23.84  thf('6', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 23.62/23.84           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['4', '5'])).
% 23.62/23.84  thf('7', plain,
% 23.62/23.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 23.62/23.84           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t91_xboole_1])).
% 23.62/23.84  thf('8', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 23.62/23.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 23.62/23.84  thf('9', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['7', '8'])).
% 23.62/23.84  thf('10', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['6', '9'])).
% 23.62/23.84  thf('11', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ 
% 23.62/23.84           (k2_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['3', '10'])).
% 23.62/23.84  thf(commutativity_k3_xboole_0, axiom,
% 23.62/23.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 23.62/23.84  thf('12', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('13', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 23.62/23.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 23.62/23.84  thf('14', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 23.62/23.84           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['4', '5'])).
% 23.62/23.84  thf('15', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['13', '14'])).
% 23.62/23.84  thf('16', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('17', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 23.62/23.84              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['15', '16'])).
% 23.62/23.84  thf(t1_boole, axiom,
% 23.62/23.84    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 23.62/23.84  thf('18', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 23.62/23.84      inference('cnf', [status(esa)], [t1_boole])).
% 23.62/23.84  thf('19', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((X0)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 23.62/23.84              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['17', '18'])).
% 23.62/23.84  thf('20', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((X0)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 23.62/23.84              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['12', '19'])).
% 23.62/23.84  thf('21', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('22', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['20', '21'])).
% 23.62/23.84  thf('23', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['11', '22'])).
% 23.62/23.84  thf('24', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 23.62/23.84           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['4', '5'])).
% 23.62/23.84  thf('25', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 23.62/23.84           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['23', '24'])).
% 23.62/23.84  thf('26', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['13', '14'])).
% 23.62/23.84  thf('27', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('28', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['25', '26', '27'])).
% 23.62/23.84  thf('29', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['20', '21'])).
% 23.62/23.84  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['28', '29'])).
% 23.62/23.84  thf('31', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['2', '30'])).
% 23.62/23.84  thf('32', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['20', '21'])).
% 23.62/23.84  thf('33', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf(t48_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 23.62/23.84  thf('34', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf(t41_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i,C:$i]:
% 23.62/23.84     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 23.62/23.84       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 23.62/23.84  thf('35', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('36', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 23.62/23.84           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['34', '35'])).
% 23.62/23.84  thf('37', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 23.62/23.84           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['33', '36'])).
% 23.62/23.84  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['28', '29'])).
% 23.62/23.84  thf(t100_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 23.62/23.84  thf('39', plain,
% 23.62/23.84      (![X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X2 @ X3)
% 23.62/23.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 23.62/23.84  thf('40', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['38', '39'])).
% 23.62/23.84  thf(t51_xboole_1, axiom,
% 23.62/23.84    (![A:$i,B:$i]:
% 23.62/23.84     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 23.62/23.84       ( A ) ))).
% 23.62/23.84  thf('41', plain,
% 23.62/23.84      (![X10 : $i, X11 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 23.62/23.84           = (X10))),
% 23.62/23.84      inference('cnf', [status(esa)], [t51_xboole_1])).
% 23.62/23.84  thf('42', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 23.62/23.84           (k3_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['40', '41'])).
% 23.62/23.84  thf('43', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf('44', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('45', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('46', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 23.62/23.84           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['44', '45'])).
% 23.62/23.84  thf('47', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 23.62/23.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['43', '46'])).
% 23.62/23.84  thf('48', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf('49', plain,
% 23.62/23.84      (![X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X2 @ X3)
% 23.62/23.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 23.62/23.84  thf('50', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 23.62/23.84  thf('52', plain,
% 23.62/23.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['42', '51'])).
% 23.62/23.84  thf('53', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('54', plain,
% 23.62/23.84      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['52', '53'])).
% 23.62/23.84  thf('55', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['38', '39'])).
% 23.62/23.84  thf('56', plain,
% 23.62/23.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['42', '51'])).
% 23.62/23.84  thf('57', plain,
% 23.62/23.84      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['55', '56'])).
% 23.62/23.84  thf('58', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('demod', [status(thm)], ['37', '54', '57'])).
% 23.62/23.84  thf('59', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('60', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 23.62/23.84           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['58', '59'])).
% 23.62/23.84  thf('61', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['13', '14'])).
% 23.62/23.84  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['28', '29'])).
% 23.62/23.84  thf('63', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['61', '62'])).
% 23.62/23.84  thf('64', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['60', '63'])).
% 23.62/23.84  thf('65', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['1', '64'])).
% 23.62/23.84  thf('66', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('67', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['65', '66'])).
% 23.62/23.84  thf('68', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 23.62/23.84  thf('69', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 23.62/23.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 23.62/23.84  thf('70', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('71', plain,
% 23.62/23.84      (![X0 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ X0)
% 23.62/23.84           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['69', '70'])).
% 23.62/23.84  thf('72', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['20', '21'])).
% 23.62/23.84  thf('73', plain,
% 23.62/23.84      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['71', '72'])).
% 23.62/23.84  thf('74', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['68', '73'])).
% 23.62/23.84  thf('75', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('76', plain,
% 23.62/23.84      (![X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X2 @ X3)
% 23.62/23.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 23.62/23.84  thf('77', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X0 @ X1)
% 23.62/23.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['75', '76'])).
% 23.62/23.84  thf('78', plain,
% 23.62/23.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['74', '77'])).
% 23.62/23.84  thf('79', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ X15) = (k1_xboole_0))),
% 23.62/23.84      inference('cnf', [status(esa)], [t92_xboole_1])).
% 23.62/23.84  thf('80', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['78', '79'])).
% 23.62/23.84  thf('81', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('82', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('83', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 23.62/23.84           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['81', '82'])).
% 23.62/23.84  thf('84', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 23.62/23.84           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['80', '83'])).
% 23.62/23.84  thf('85', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['61', '62'])).
% 23.62/23.84  thf('86', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 23.62/23.84           = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['84', '85'])).
% 23.62/23.84  thf('87', plain,
% 23.62/23.84      (![X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X2 @ X3)
% 23.62/23.84           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 23.62/23.84  thf('88', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('89', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('demod', [status(thm)], ['37', '54', '57'])).
% 23.62/23.84  thf('90', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0)
% 23.62/23.84           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['88', '89'])).
% 23.62/23.84  thf('91', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0)
% 23.62/23.84           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 23.62/23.84              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['87', '90'])).
% 23.62/23.84  thf('92', plain,
% 23.62/23.84      (![X10 : $i, X11 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 23.62/23.84           = (X10))),
% 23.62/23.84      inference('cnf', [status(esa)], [t51_xboole_1])).
% 23.62/23.84  thf('93', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('demod', [status(thm)], ['37', '54', '57'])).
% 23.62/23.84  thf('94', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['92', '93'])).
% 23.62/23.84  thf('95', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('96', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 23.62/23.84           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['94', '95'])).
% 23.62/23.84  thf('97', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['61', '62'])).
% 23.62/23.84  thf('98', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['96', '97'])).
% 23.62/23.84  thf('99', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('100', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('demod', [status(thm)], ['91', '98', '99'])).
% 23.62/23.84  thf('101', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('102', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 23.62/23.84           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['100', '101'])).
% 23.62/23.84  thf('103', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf('104', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['102', '103'])).
% 23.62/23.84  thf('105', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X0 @ X1)
% 23.62/23.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['75', '76'])).
% 23.62/23.84  thf('106', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['7', '8'])).
% 23.62/23.84  thf('107', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 23.62/23.84           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['4', '5'])).
% 23.62/23.84  thf('108', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['28', '29'])).
% 23.62/23.84  thf('109', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['107', '108'])).
% 23.62/23.84  thf('110', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['106', '109'])).
% 23.62/23.84  thf('111', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['61', '62'])).
% 23.62/23.84  thf('112', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 23.62/23.84      inference('demod', [status(thm)], ['110', '111'])).
% 23.62/23.84  thf('113', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (X1))),
% 23.62/23.84      inference('sup+', [status(thm)], ['105', '112'])).
% 23.62/23.84  thf('114', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['104', '113'])).
% 23.62/23.84  thf('115', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('116', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['114', '115'])).
% 23.62/23.84  thf('117', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 23.62/23.84           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['86', '116'])).
% 23.62/23.84  thf('118', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 23.62/23.84           = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['84', '85'])).
% 23.62/23.84  thf('119', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 23.62/23.84           = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['117', '118'])).
% 23.62/23.84  thf('120', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 23.62/23.84           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['34', '35'])).
% 23.62/23.84  thf('121', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 23.62/23.84           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['119', '120'])).
% 23.62/23.84  thf('122', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('123', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 23.62/23.84      inference('demod', [status(thm)], ['37', '54', '57'])).
% 23.62/23.84  thf('124', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('125', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 23.62/23.84           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['123', '124'])).
% 23.62/23.84  thf('126', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.84  thf('127', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['125', '126'])).
% 23.62/23.84  thf('128', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X1 @ X0)
% 23.62/23.84           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['121', '122', '127'])).
% 23.62/23.84  thf('129', plain,
% 23.62/23.84      (![X10 : $i, X11 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 23.62/23.84           = (X10))),
% 23.62/23.84      inference('cnf', [status(esa)], [t51_xboole_1])).
% 23.62/23.84  thf('130', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 23.62/23.84           (k4_xboole_0 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['128', '129'])).
% 23.62/23.84  thf('131', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('132', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['102', '103'])).
% 23.62/23.84  thf('133', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['130', '131', '132'])).
% 23.62/23.84  thf('134', plain,
% 23.62/23.84      (![X18 : $i, X19 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.84           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.84  thf('135', plain,
% 23.62/23.84      (![X16 : $i, X17 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X16 @ X17)
% 23.62/23.84           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 23.62/23.84              (k3_xboole_0 @ X16 @ X17)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t93_xboole_1])).
% 23.62/23.84  thf('136', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 23.62/23.84           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 23.62/23.84              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['134', '135'])).
% 23.62/23.84  thf('137', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 23.62/23.84  thf('138', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['60', '63'])).
% 23.62/23.84  thf('139', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('140', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('141', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 23.62/23.84           = (k4_xboole_0 @ X2 @ 
% 23.62/23.84              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['139', '140'])).
% 23.62/23.84  thf('142', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('143', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 23.62/23.84           = (k4_xboole_0 @ X2 @ 
% 23.62/23.84              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 23.62/23.84      inference('demod', [status(thm)], ['141', '142'])).
% 23.62/23.84  thf('144', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 23.62/23.84           = (k4_xboole_0 @ X2 @ 
% 23.62/23.84              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 23.62/23.84               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['138', '143'])).
% 23.62/23.84  thf('145', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('146', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['78', '79'])).
% 23.62/23.84  thf('147', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('148', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k1_xboole_0)
% 23.62/23.84           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 23.62/23.84      inference('sup+', [status(thm)], ['146', '147'])).
% 23.62/23.84  thf('149', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k1_xboole_0))),
% 23.62/23.84      inference('demod', [status(thm)], ['144', '145', '148'])).
% 23.62/23.84  thf('150', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['137', '149'])).
% 23.62/23.84  thf('151', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 23.62/23.84      inference('cnf', [status(esa)], [t1_boole])).
% 23.62/23.84  thf('152', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['136', '150', '151'])).
% 23.62/23.84  thf('153', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('sup+', [status(thm)], ['133', '152'])).
% 23.62/23.84  thf('154', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['68', '73'])).
% 23.62/23.84  thf('155', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('156', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('157', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 23.62/23.84           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['155', '156'])).
% 23.62/23.84  thf('158', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('159', plain,
% 23.62/23.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.84           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.84  thf('160', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 23.62/23.84           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 23.62/23.84      inference('demod', [status(thm)], ['157', '158', '159'])).
% 23.62/23.84  thf('161', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('162', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X3 @ 
% 23.62/23.84           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 23.62/23.84           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 23.62/23.84      inference('sup+', [status(thm)], ['160', '161'])).
% 23.62/23.84  thf('163', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('164', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['162', '163'])).
% 23.62/23.84  thf('165', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 23.62/23.84           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['154', '164'])).
% 23.62/23.84  thf('166', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('167', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.62/23.84         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['162', '163'])).
% 23.62/23.84  thf('168', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['68', '73'])).
% 23.62/23.84  thf('169', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 23.62/23.84  thf('170', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 23.62/23.84           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 23.62/23.84      inference('sup+', [status(thm)], ['153', '169'])).
% 23.62/23.84  thf('171', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['67', '170'])).
% 23.62/23.84  thf('172', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X1 @ X0)
% 23.62/23.84           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['121', '122', '127'])).
% 23.62/23.84  thf('173', plain,
% 23.62/23.84      (![X8 : $i, X9 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 23.62/23.84           = (k3_xboole_0 @ X8 @ X9))),
% 23.62/23.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 23.62/23.84  thf('174', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 23.62/23.84      inference('sup+', [status(thm)], ['172', '173'])).
% 23.62/23.84  thf('175', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 23.62/23.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 23.62/23.84  thf('176', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.84      inference('demod', [status(thm)], ['102', '103'])).
% 23.62/23.84  thf('177', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.84           = (X0))),
% 23.62/23.84      inference('demod', [status(thm)], ['174', '175', '176'])).
% 23.62/23.84  thf('178', plain,
% 23.62/23.84      (![X0 : $i, X1 : $i]:
% 23.62/23.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 23.62/23.84           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 23.62/23.84           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['171', '177'])).
% 23.62/23.85  thf('179', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['107', '108'])).
% 23.62/23.85  thf('180', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k1_xboole_0)
% 23.62/23.85           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['88', '89'])).
% 23.62/23.85  thf('181', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k1_xboole_0)
% 23.62/23.85           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))),
% 23.62/23.85      inference('sup+', [status(thm)], ['179', '180'])).
% 23.62/23.85  thf('182', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 23.62/23.85      inference('demod', [status(thm)], ['31', '32'])).
% 23.62/23.85  thf('183', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k2_xboole_0 @ X1 @ X0)
% 23.62/23.85           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['178', '181', '182'])).
% 23.62/23.85  thf('184', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k2_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('demod', [status(thm)], ['130', '131', '132'])).
% 23.62/23.85  thf('185', plain,
% 23.62/23.85      (![X18 : $i, X19 : $i]:
% 23.62/23.85         ((k2_xboole_0 @ X18 @ X19)
% 23.62/23.85           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 23.62/23.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 23.62/23.85  thf('186', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['107', '108'])).
% 23.62/23.85  thf('187', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X0 @ X1)
% 23.62/23.85           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['185', '186'])).
% 23.62/23.85  thf('188', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 23.62/23.85           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['184', '187'])).
% 23.62/23.85  thf('189', plain,
% 23.62/23.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 23.62/23.85           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 23.62/23.85      inference('cnf', [status(esa)], [t41_xboole_1])).
% 23.62/23.85  thf('190', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 23.62/23.85      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 23.62/23.85  thf('191', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X1 @ X0)
% 23.62/23.85           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['188', '189', '190'])).
% 23.62/23.85  thf('192', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['183', '191'])).
% 23.62/23.85  thf('193', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 23.62/23.85      inference('demod', [status(thm)], ['110', '111'])).
% 23.62/23.85  thf('194', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['107', '108'])).
% 23.62/23.85  thf('195', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('sup+', [status(thm)], ['193', '194'])).
% 23.62/23.85  thf('196', plain,
% 23.62/23.85      (![X12 : $i, X13 : $i, X14 : $i]:
% 23.62/23.85         ((k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ X14)
% 23.62/23.85           = (k5_xboole_0 @ X12 @ (k5_xboole_0 @ X13 @ X14)))),
% 23.62/23.85      inference('cnf', [status(esa)], [t91_xboole_1])).
% 23.62/23.85  thf('197', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.85         ((k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X2)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['195', '196'])).
% 23.62/23.85  thf('198', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('sup+', [status(thm)], ['193', '194'])).
% 23.62/23.85  thf('199', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.62/23.85         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1)
% 23.62/23.85           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['197', '198'])).
% 23.62/23.85  thf('200', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('sup+', [status(thm)], ['193', '194'])).
% 23.62/23.85  thf('201', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X0 @ X1)
% 23.62/23.85           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['185', '186'])).
% 23.62/23.85  thf('202', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 23.62/23.85      inference('demod', [status(thm)], ['192', '199', '200', '201'])).
% 23.62/23.85  thf('203', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X0 @ X1)
% 23.62/23.85           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['75', '76'])).
% 23.62/23.85  thf('204', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['107', '108'])).
% 23.62/23.85  thf('205', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k3_xboole_0 @ X0 @ X1)
% 23.62/23.85           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('sup+', [status(thm)], ['203', '204'])).
% 23.62/23.85  thf('206', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k3_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('demod', [status(thm)], ['202', '205'])).
% 23.62/23.85  thf('207', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (X0))),
% 23.62/23.85      inference('demod', [status(thm)], ['174', '175', '176'])).
% 23.62/23.85  thf('208', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 23.62/23.85           (k3_xboole_0 @ X1 @ X0)) = (k5_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('sup+', [status(thm)], ['206', '207'])).
% 23.62/23.85  thf('209', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k2_xboole_0 @ X1 @ X0)
% 23.62/23.85           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 23.62/23.85      inference('demod', [status(thm)], ['178', '181', '182'])).
% 23.62/23.85  thf('210', plain,
% 23.62/23.85      (![X0 : $i, X1 : $i]:
% 23.62/23.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 23.62/23.85           = (k5_xboole_0 @ X1 @ X0))),
% 23.62/23.85      inference('demod', [status(thm)], ['208', '209'])).
% 23.62/23.85  thf('211', plain,
% 23.62/23.85      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 23.62/23.85      inference('demod', [status(thm)], ['0', '210'])).
% 23.62/23.85  thf('212', plain, ($false), inference('simplify', [status(thm)], ['211'])).
% 23.62/23.85  
% 23.62/23.85  % SZS output end Refutation
% 23.62/23.85  
% 23.62/23.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
