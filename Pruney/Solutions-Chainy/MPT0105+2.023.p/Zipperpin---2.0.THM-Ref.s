%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7O8nwVycB

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:07 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  171 (2421 expanded)
%              Number of leaves         :   18 ( 823 expanded)
%              Depth                    :   27
%              Number of atoms          : 1478 (18296 expanded)
%              Number of equality atoms :  163 (2413 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','56'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['74','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('111',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','109','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','123','124','125'])).

thf('127',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','128'])).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('141',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('142',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['86','104'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','56'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['129','149'])).

thf('151',plain,(
    $false ),
    inference(simplify,[status(thm)],['150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7O8nwVycB
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.57/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.57/1.78  % Solved by: fo/fo7.sh
% 1.57/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.57/1.78  % done 1558 iterations in 1.311s
% 1.57/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.57/1.78  % SZS output start Refutation
% 1.57/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.57/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.57/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.57/1.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.57/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.57/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.57/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.57/1.78  thf(t98_xboole_1, conjecture,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.57/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.57/1.78    (~( ![A:$i,B:$i]:
% 1.57/1.78        ( ( k2_xboole_0 @ A @ B ) =
% 1.57/1.78          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 1.57/1.78    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 1.57/1.78  thf('0', plain,
% 1.57/1.78      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.57/1.78         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(t1_boole, axiom,
% 1.57/1.78    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.57/1.78  thf('1', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf(t46_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.57/1.78  thf('2', plain,
% 1.57/1.78      (![X11 : $i, X12 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 1.57/1.78      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.57/1.78  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.57/1.78  thf(t41_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.57/1.78       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.57/1.78  thf('4', plain,
% 1.57/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.57/1.78           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.57/1.78  thf('5', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k1_xboole_0)
% 1.57/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('sup+', [status(thm)], ['3', '4'])).
% 1.57/1.78  thf(t39_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.57/1.78  thf('6', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('7', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['5', '6'])).
% 1.57/1.78  thf(t48_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.57/1.78  thf('8', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('9', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.57/1.78           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['7', '8'])).
% 1.57/1.78  thf(t3_boole, axiom,
% 1.57/1.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.57/1.78  thf('10', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.57/1.78  thf('11', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.57/1.78  thf(l98_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k5_xboole_0 @ A @ B ) =
% 1.57/1.78       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.57/1.78  thf('12', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('13', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('14', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['12', '13'])).
% 1.57/1.78  thf('15', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.57/1.78              (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('sup+', [status(thm)], ['11', '14'])).
% 1.57/1.78  thf('16', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.57/1.78  thf('17', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('demod', [status(thm)], ['15', '16'])).
% 1.57/1.78  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.57/1.78  thf('19', plain,
% 1.57/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.57/1.78           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.57/1.78  thf('20', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('21', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['19', '20'])).
% 1.57/1.78  thf('22', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.57/1.78           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['18', '21'])).
% 1.57/1.78  thf('23', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf('24', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1)
% 1.57/1.78           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['22', '23'])).
% 1.57/1.78  thf('25', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.57/1.78  thf(t94_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( k2_xboole_0 @ A @ B ) =
% 1.57/1.78       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.57/1.78  thf('26', plain,
% 1.57/1.78      (![X18 : $i, X19 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X18 @ X19)
% 1.57/1.78           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.57/1.78              (k3_xboole_0 @ X18 @ X19)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.57/1.78  thf(t91_xboole_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.57/1.78       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.57/1.78  thf('27', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('28', plain,
% 1.57/1.78      (![X18 : $i, X19 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X18 @ X19)
% 1.57/1.78           = (k5_xboole_0 @ X18 @ 
% 1.57/1.78              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 1.57/1.78      inference('demod', [status(thm)], ['26', '27'])).
% 1.57/1.78  thf('29', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['25', '28'])).
% 1.57/1.78  thf(commutativity_k5_xboole_0, axiom,
% 1.57/1.78    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.57/1.78  thf('30', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('31', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('demod', [status(thm)], ['29', '30'])).
% 1.57/1.78  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.57/1.78  thf('33', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('34', plain,
% 1.57/1.78      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['32', '33'])).
% 1.57/1.78  thf('35', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf('36', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['34', '35'])).
% 1.57/1.78  thf('37', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('38', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ X0)
% 1.57/1.78           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['36', '37'])).
% 1.57/1.78  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.57/1.78  thf('40', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('41', plain,
% 1.57/1.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['39', '40'])).
% 1.57/1.78  thf('42', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_boole])).
% 1.57/1.78  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['41', '42'])).
% 1.57/1.78  thf('44', plain,
% 1.57/1.78      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['38', '43'])).
% 1.57/1.78  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['1', '2'])).
% 1.57/1.78  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('47', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('48', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.57/1.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['46', '47'])).
% 1.57/1.78  thf('49', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['41', '42'])).
% 1.57/1.78  thf('50', plain,
% 1.57/1.78      (![X18 : $i, X19 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X18 @ X19)
% 1.57/1.78           = (k5_xboole_0 @ X18 @ 
% 1.57/1.78              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 1.57/1.78      inference('demod', [status(thm)], ['26', '27'])).
% 1.57/1.78  thf('51', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ X0)
% 1.57/1.78           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['49', '50'])).
% 1.57/1.78  thf('52', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['34', '35'])).
% 1.57/1.78  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('54', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.57/1.78      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.57/1.78  thf('55', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['54', '55'])).
% 1.57/1.78  thf('57', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['48', '56'])).
% 1.57/1.78  thf('58', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['31', '57'])).
% 1.57/1.78  thf('59', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 1.57/1.78           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['24', '58'])).
% 1.57/1.78  thf('60', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1)
% 1.57/1.78           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['22', '23'])).
% 1.57/1.78  thf('61', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 1.57/1.78           = (X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['59', '60'])).
% 1.57/1.78  thf('62', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('63', plain,
% 1.57/1.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.57/1.78           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.57/1.78  thf('64', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.57/1.78           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['62', '63'])).
% 1.57/1.78  thf('65', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['61', '64'])).
% 1.57/1.78  thf('66', plain,
% 1.57/1.78      (![X11 : $i, X12 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 1.57/1.78      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.57/1.78  thf('67', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('68', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 1.57/1.78           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['66', '67'])).
% 1.57/1.78  thf('69', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf('70', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ X1)
% 1.57/1.78           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['68', '69'])).
% 1.57/1.78  thf('71', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('72', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['70', '71'])).
% 1.57/1.78  thf('73', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('74', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['72', '73'])).
% 1.57/1.78  thf('75', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['5', '6'])).
% 1.57/1.78  thf('76', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['19', '20'])).
% 1.57/1.78  thf('77', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.57/1.78           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['75', '76'])).
% 1.57/1.78  thf('78', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf('79', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['77', '78'])).
% 1.57/1.78  thf('80', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('81', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 1.57/1.78      inference('sup+', [status(thm)], ['79', '80'])).
% 1.57/1.78  thf('82', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('83', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('84', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['82', '83'])).
% 1.57/1.78  thf('85', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('86', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['81', '84', '85'])).
% 1.57/1.78  thf('87', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['77', '78'])).
% 1.57/1.78  thf('88', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['9', '10'])).
% 1.57/1.78  thf('89', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X0 @ X1)
% 1.57/1.78           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['87', '88'])).
% 1.57/1.78  thf('90', plain,
% 1.57/1.78      (![X18 : $i, X19 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X18 @ X19)
% 1.57/1.78           = (k5_xboole_0 @ X18 @ 
% 1.57/1.78              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 1.57/1.78      inference('demod', [status(thm)], ['26', '27'])).
% 1.57/1.78  thf('91', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.57/1.78           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('sup+', [status(thm)], ['89', '90'])).
% 1.57/1.78  thf('92', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('93', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['48', '56'])).
% 1.57/1.78  thf('94', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['92', '93'])).
% 1.57/1.78  thf('95', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '94'])).
% 1.57/1.78  thf('96', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('97', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.57/1.78           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['95', '96'])).
% 1.57/1.78  thf('98', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('99', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X0 @ X1)
% 1.57/1.78           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['87', '88'])).
% 1.57/1.78  thf('100', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['97', '98', '99'])).
% 1.57/1.78  thf('101', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['81', '84', '85'])).
% 1.57/1.78  thf('102', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['100', '101'])).
% 1.57/1.78  thf('103', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.57/1.78           = (k3_xboole_0 @ X13 @ X14))),
% 1.57/1.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.57/1.78  thf('104', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k3_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['102', '103'])).
% 1.57/1.78  thf('105', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k3_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['86', '104'])).
% 1.57/1.78  thf('106', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['74', '105'])).
% 1.57/1.78  thf('107', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['92', '93'])).
% 1.57/1.78  thf('108', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k3_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['102', '103'])).
% 1.57/1.78  thf('109', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.57/1.78  thf('110', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['5', '6'])).
% 1.57/1.78  thf('111', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('112', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.57/1.78           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['110', '111'])).
% 1.57/1.78  thf('113', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [t1_boole])).
% 1.57/1.78  thf('114', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X1 @ X0)
% 1.57/1.78           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['112', '113'])).
% 1.57/1.78  thf('115', plain,
% 1.57/1.78      (![X2 : $i, X3 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X2 @ X3)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 1.57/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.57/1.78  thf('116', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['114', '115'])).
% 1.57/1.78  thf('117', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('118', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.57/1.78              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['116', '117'])).
% 1.57/1.78  thf('119', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['31', '57'])).
% 1.57/1.78  thf('120', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.57/1.78  thf('121', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['119', '120'])).
% 1.57/1.78  thf('122', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['118', '121'])).
% 1.57/1.78  thf('123', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X1 @ X0)
% 1.57/1.78           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['65', '109', '122'])).
% 1.57/1.78  thf('124', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['31', '57'])).
% 1.57/1.78  thf('125', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['31', '57'])).
% 1.57/1.78  thf('126', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.57/1.78           = (k2_xboole_0 @ X1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['17', '123', '124', '125'])).
% 1.57/1.78  thf('127', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.57/1.78           = (k2_xboole_0 @ X5 @ X6))),
% 1.57/1.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.57/1.78  thf('128', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('sup+', [status(thm)], ['126', '127'])).
% 1.57/1.78  thf('129', plain,
% 1.57/1.78      (((k2_xboole_0 @ sk_B @ sk_A)
% 1.57/1.78         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.57/1.78      inference('demod', [status(thm)], ['0', '128'])).
% 1.57/1.78  thf('130', plain,
% 1.57/1.78      (![X18 : $i, X19 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X18 @ X19)
% 1.57/1.78           = (k5_xboole_0 @ X18 @ 
% 1.57/1.78              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 1.57/1.78      inference('demod', [status(thm)], ['26', '27'])).
% 1.57/1.78  thf('131', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['92', '93'])).
% 1.57/1.78  thf('132', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1)
% 1.57/1.78           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.57/1.78              (k2_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['130', '131'])).
% 1.57/1.78  thf('133', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('134', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X1)
% 1.57/1.78           = (k5_xboole_0 @ X0 @ 
% 1.57/1.78              (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 1.57/1.78      inference('demod', [status(thm)], ['132', '133'])).
% 1.57/1.78  thf('135', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('136', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('137', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.57/1.78           = (k1_xboole_0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['135', '136'])).
% 1.57/1.78  thf('138', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('139', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.57/1.78           = (k5_xboole_0 @ X2 @ 
% 1.57/1.78              (k5_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1)) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['137', '138'])).
% 1.57/1.78  thf('140', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.57/1.78      inference('sup+', [status(thm)], ['54', '55'])).
% 1.57/1.78  thf('141', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('142', plain,
% 1.57/1.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.57/1.78           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.57/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.57/1.78  thf('143', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((X0)
% 1.57/1.78           = (k5_xboole_0 @ X2 @ 
% 1.57/1.78              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))))),
% 1.57/1.78      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 1.57/1.78  thf('144', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ X1)
% 1.57/1.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['134', '143'])).
% 1.57/1.78  thf('145', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.57/1.78  thf('146', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.57/1.78           = (k3_xboole_0 @ X0 @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['86', '104'])).
% 1.57/1.78  thf('147', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('demod', [status(thm)], ['48', '56'])).
% 1.57/1.78  thf('148', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k4_xboole_0 @ X1 @ X0)
% 1.57/1.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.57/1.78      inference('sup+', [status(thm)], ['146', '147'])).
% 1.57/1.78  thf('149', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((k2_xboole_0 @ X0 @ X1)
% 1.57/1.78           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['144', '145', '148'])).
% 1.57/1.78  thf('150', plain,
% 1.57/1.78      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['129', '149'])).
% 1.57/1.78  thf('151', plain, ($false), inference('simplify', [status(thm)], ['150'])).
% 1.57/1.78  
% 1.57/1.78  % SZS output end Refutation
% 1.57/1.78  
% 1.57/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
