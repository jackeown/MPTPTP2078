%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LWkQaY1evI

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:24 EST 2020

% Result     : Theorem 24.46s
% Output     : Refutation 24.46s
% Verified   : 
% Statistics : Number of formulae       :  233 (131929 expanded)
%              Number of leaves         :   18 (46701 expanded)
%              Depth                    :   40
%              Number of atoms          : 1976 (1174864 expanded)
%              Number of equality atoms :  225 (131921 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26','36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('80',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('81',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('82',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78','79','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['65','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('95',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['72','88'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','19','20'])).

thf('105',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78','79','86','87'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('121',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['93','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['92','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','126'])).

thf('128',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','90'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['65','89'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','121'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('148',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('152',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('153',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('156',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ X6 )
      = ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('161',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['65','89'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['151','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','173'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['150','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['141','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('182',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['102','121'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['180','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','54'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['188','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('199',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['197','200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

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
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['188','191','192'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','211'])).

thf('213',plain,(
    $false ),
    inference(simplify,[status(thm)],['212'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LWkQaY1evI
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:43:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 24.46/24.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.46/24.72  % Solved by: fo/fo7.sh
% 24.46/24.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.46/24.72  % done 13188 iterations in 24.237s
% 24.46/24.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.46/24.72  % SZS output start Refutation
% 24.46/24.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.46/24.72  thf(sk_A_type, type, sk_A: $i).
% 24.46/24.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 24.46/24.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.46/24.72  thf(sk_B_type, type, sk_B: $i).
% 24.46/24.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.46/24.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 24.46/24.72  thf(t101_xboole_1, conjecture,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k5_xboole_0 @ A @ B ) =
% 24.46/24.72       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 24.46/24.72  thf(zf_stmt_0, negated_conjecture,
% 24.46/24.72    (~( ![A:$i,B:$i]:
% 24.46/24.72        ( ( k5_xboole_0 @ A @ B ) =
% 24.46/24.72          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 24.46/24.72    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 24.46/24.72  thf('0', plain,
% 24.46/24.72      (((k5_xboole_0 @ sk_A @ sk_B)
% 24.46/24.72         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 24.46/24.72             (k3_xboole_0 @ sk_A @ sk_B)))),
% 24.46/24.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.46/24.72  thf(t93_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k2_xboole_0 @ A @ B ) =
% 24.46/24.72       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 24.46/24.72  thf('1', plain,
% 24.46/24.72      (![X17 : $i, X18 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X17 @ X18)
% 24.46/24.72           = (k2_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 24.46/24.72              (k3_xboole_0 @ X17 @ X18)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t93_xboole_1])).
% 24.46/24.72  thf(t48_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 24.46/24.72  thf('2', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('3', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('4', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['2', '3'])).
% 24.46/24.72  thf(commutativity_k3_xboole_0, axiom,
% 24.46/24.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 24.46/24.72  thf('5', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf(t47_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 24.46/24.72  thf('6', plain,
% 24.46/24.72      (![X7 : $i, X8 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 24.46/24.72           = (k4_xboole_0 @ X7 @ X8))),
% 24.46/24.72      inference('cnf', [status(esa)], [t47_xboole_1])).
% 24.46/24.72  thf('7', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['5', '6'])).
% 24.46/24.72  thf('8', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['4', '7'])).
% 24.46/24.72  thf('9', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['2', '3'])).
% 24.46/24.72  thf('10', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))))),
% 24.46/24.72      inference('sup+', [status(thm)], ['8', '9'])).
% 24.46/24.72  thf('11', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('12', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('13', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X0 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['10', '11', '12'])).
% 24.46/24.72  thf('14', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['4', '7'])).
% 24.46/24.72  thf(t100_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 24.46/24.72  thf('15', plain,
% 24.46/24.72      (![X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X2 @ X3)
% 24.46/24.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 24.46/24.72  thf('16', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['14', '15'])).
% 24.46/24.72  thf('17', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf(t98_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 24.46/24.72  thf('18', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('19', plain,
% 24.46/24.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 24.46/24.72  thf('20', plain,
% 24.46/24.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 24.46/24.72  thf('21', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['13', '19', '20'])).
% 24.46/24.72  thf('22', plain,
% 24.46/24.72      (![X7 : $i, X8 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 24.46/24.72           = (k4_xboole_0 @ X7 @ X8))),
% 24.46/24.72      inference('cnf', [status(esa)], [t47_xboole_1])).
% 24.46/24.72  thf('23', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('24', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['22', '23'])).
% 24.46/24.72  thf('25', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ X0)
% 24.46/24.72           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ 
% 24.46/24.72              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))))),
% 24.46/24.72      inference('sup+', [status(thm)], ['21', '24'])).
% 24.46/24.72  thf('26', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['13', '19', '20'])).
% 24.46/24.72  thf('27', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['2', '3'])).
% 24.46/24.72  thf('28', plain,
% 24.46/24.72      (![X7 : $i, X8 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8))
% 24.46/24.72           = (k4_xboole_0 @ X7 @ X8))),
% 24.46/24.72      inference('cnf', [status(esa)], [t47_xboole_1])).
% 24.46/24.72  thf('29', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['27', '28'])).
% 24.46/24.72  thf('30', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('31', plain,
% 24.46/24.72      (![X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X2 @ X3)
% 24.46/24.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 24.46/24.72  thf('32', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['30', '31'])).
% 24.46/24.72  thf('33', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['29', '32'])).
% 24.46/24.72  thf(t41_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i,C:$i]:
% 24.46/24.72     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 24.46/24.72       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 24.46/24.72  thf('34', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf(t92_xboole_1, axiom,
% 24.46/24.72    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 24.46/24.72  thf('35', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 24.46/24.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 24.46/24.72  thf('36', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('37', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['13', '19', '20'])).
% 24.46/24.72  thf(t51_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i]:
% 24.46/24.72     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 24.46/24.72       ( A ) ))).
% 24.46/24.72  thf('38', plain,
% 24.46/24.72      (![X11 : $i, X12 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 24.46/24.72           = (X11))),
% 24.46/24.72      inference('cnf', [status(esa)], [t51_xboole_1])).
% 24.46/24.72  thf('39', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ 
% 24.46/24.72           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))) = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['37', '38'])).
% 24.46/24.72  thf('40', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('41', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['39', '40'])).
% 24.46/24.72  thf('42', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('43', plain,
% 24.46/24.72      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['41', '42'])).
% 24.46/24.72  thf('44', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('45', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['43', '44'])).
% 24.46/24.72  thf('46', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0)
% 24.46/24.72           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['25', '26', '36', '45'])).
% 24.46/24.72  thf('47', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['39', '40'])).
% 24.46/24.72  thf('48', plain,
% 24.46/24.72      (![X0 : $i]: ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['46', '47'])).
% 24.46/24.72  thf('49', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['48', '49'])).
% 24.46/24.72  thf('51', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf('52', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 24.46/24.72           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['50', '51'])).
% 24.46/24.72  thf('53', plain,
% 24.46/24.72      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['41', '42'])).
% 24.46/24.72  thf('54', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['52', '53'])).
% 24.46/24.72  thf('55', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k1_xboole_0)
% 24.46/24.72           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['1', '54'])).
% 24.46/24.72  thf('56', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['52', '53'])).
% 24.46/24.72  thf('57', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('58', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 24.46/24.72           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['56', '57'])).
% 24.46/24.72  thf('59', plain,
% 24.46/24.72      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['41', '42'])).
% 24.46/24.72  thf('60', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('61', plain,
% 24.46/24.72      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['59', '60'])).
% 24.46/24.72  thf('62', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['30', '31'])).
% 24.46/24.72  thf('63', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['61', '62'])).
% 24.46/24.72  thf('64', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['43', '44'])).
% 24.46/24.72  thf('65', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['63', '64'])).
% 24.46/24.72  thf('66', plain,
% 24.46/24.72      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['59', '60'])).
% 24.46/24.72  thf('67', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('68', plain,
% 24.46/24.72      (![X11 : $i, X12 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 24.46/24.72           = (X11))),
% 24.46/24.72      inference('cnf', [status(esa)], [t51_xboole_1])).
% 24.46/24.72  thf('69', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 24.46/24.72           = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['67', '68'])).
% 24.46/24.72  thf('70', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['66', '69'])).
% 24.46/24.72  thf('71', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['63', '64'])).
% 24.46/24.72  thf('72', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['70', '71'])).
% 24.46/24.72  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['48', '49'])).
% 24.46/24.72  thf('74', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('75', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('76', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['74', '75'])).
% 24.46/24.72  thf('77', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 24.46/24.72           = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['73', '76'])).
% 24.46/24.72  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['48', '49'])).
% 24.46/24.72  thf('79', plain,
% 24.46/24.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 24.46/24.72  thf('80', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 24.46/24.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 24.46/24.72  thf('81', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 24.46/24.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 24.46/24.72  thf(t91_xboole_1, axiom,
% 24.46/24.72    (![A:$i,B:$i,C:$i]:
% 24.46/24.72     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 24.46/24.72       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 24.46/24.72  thf('82', plain,
% 24.46/24.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 24.46/24.72           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 24.46/24.72  thf('83', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['81', '82'])).
% 24.46/24.72  thf('84', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['80', '83'])).
% 24.46/24.72  thf('85', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['43', '44'])).
% 24.46/24.72  thf('86', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['84', '85'])).
% 24.46/24.72  thf('87', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['39', '40'])).
% 24.46/24.72  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['77', '78', '79', '86', '87'])).
% 24.46/24.72  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['72', '88'])).
% 24.46/24.72  thf('90', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['65', '89'])).
% 24.46/24.72  thf('91', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['58', '90'])).
% 24.46/24.72  thf('92', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('93', plain,
% 24.46/24.72      (![X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X2 @ X3)
% 24.46/24.72           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 24.46/24.72  thf('94', plain,
% 24.46/24.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 24.46/24.72           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 24.46/24.72  thf('95', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 24.46/24.72      inference('cnf', [status(esa)], [t92_xboole_1])).
% 24.46/24.72  thf('96', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 24.46/24.72           = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['94', '95'])).
% 24.46/24.72  thf('97', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['81', '82'])).
% 24.46/24.72  thf('98', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['84', '85'])).
% 24.46/24.72  thf('99', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['97', '98'])).
% 24.46/24.72  thf('100', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['72', '88'])).
% 24.46/24.72  thf('101', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['99', '100'])).
% 24.46/24.72  thf('102', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['96', '101'])).
% 24.46/24.72  thf('103', plain,
% 24.46/24.72      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 24.46/24.72  thf('104', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['13', '19', '20'])).
% 24.46/24.72  thf('105', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('106', plain,
% 24.46/24.72      (![X11 : $i, X12 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 24.46/24.72           = (X11))),
% 24.46/24.72      inference('cnf', [status(esa)], [t51_xboole_1])).
% 24.46/24.72  thf('107', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 24.46/24.72           (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['105', '106'])).
% 24.46/24.72  thf('108', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['27', '28'])).
% 24.46/24.72  thf('109', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['107', '108'])).
% 24.46/24.72  thf('110', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ 
% 24.46/24.72           (k2_xboole_0 @ X0 @ X0)) = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['104', '109'])).
% 24.46/24.72  thf('111', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('112', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['110', '111'])).
% 24.46/24.72  thf('113', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['77', '78', '79', '86', '87'])).
% 24.46/24.72  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['112', '113'])).
% 24.46/24.72  thf('115', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['103', '114'])).
% 24.46/24.72  thf('116', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['22', '23'])).
% 24.46/24.72  thf('117', plain,
% 24.46/24.72      (![X0 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['115', '116'])).
% 24.46/24.72  thf('118', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['103', '114'])).
% 24.46/24.72  thf('119', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['112', '113'])).
% 24.46/24.72  thf('120', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['48', '49'])).
% 24.46/24.72  thf('121', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 24.46/24.72  thf('122', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['102', '121'])).
% 24.46/24.72  thf('123', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['93', '122'])).
% 24.46/24.72  thf('124', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['22', '23'])).
% 24.46/24.72  thf('125', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['123', '124'])).
% 24.46/24.72  thf('126', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['92', '125'])).
% 24.46/24.72  thf('127', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 24.46/24.72           = (k2_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['91', '126'])).
% 24.46/24.72  thf('128', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('129', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['99', '100'])).
% 24.46/24.72  thf('130', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['128', '129'])).
% 24.46/24.72  thf('131', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['127', '130'])).
% 24.46/24.72  thf('132', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['128', '129'])).
% 24.46/24.72  thf('133', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 24.46/24.72           = (k4_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['131', '132'])).
% 24.46/24.72  thf('134', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('135', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['133', '134'])).
% 24.46/24.72  thf('136', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('137', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['58', '90'])).
% 24.46/24.72  thf('138', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['135', '136', '137'])).
% 24.46/24.72  thf('139', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ 
% 24.46/24.72           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 24.46/24.72           k1_xboole_0) = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['55', '138'])).
% 24.46/24.72  thf('140', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['65', '89'])).
% 24.46/24.72  thf('141', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['139', '140'])).
% 24.46/24.72  thf('142', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['102', '121'])).
% 24.46/24.72  thf('143', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['99', '100'])).
% 24.46/24.72  thf('144', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['142', '143'])).
% 24.46/24.72  thf('145', plain,
% 24.46/24.72      (![X17 : $i, X18 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X17 @ X18)
% 24.46/24.72           = (k2_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 24.46/24.72              (k3_xboole_0 @ X17 @ X18)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t93_xboole_1])).
% 24.46/24.72  thf('146', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['144', '145'])).
% 24.46/24.72  thf('147', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('148', plain,
% 24.46/24.72      (![X17 : $i, X18 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X17 @ X18)
% 24.46/24.72           = (k2_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 24.46/24.72              (k3_xboole_0 @ X17 @ X18)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t93_xboole_1])).
% 24.46/24.72  thf('149', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['147', '148'])).
% 24.46/24.72  thf('150', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['146', '149'])).
% 24.46/24.72  thf('151', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['103', '114'])).
% 24.46/24.72  thf('152', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf('153', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf('154', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 24.46/24.72           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['152', '153'])).
% 24.46/24.72  thf('155', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf('156', plain,
% 24.46/24.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ X6)
% 24.46/24.72           = (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X6)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t41_xboole_1])).
% 24.46/24.72  thf('157', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 24.46/24.72           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 24.46/24.72      inference('demod', [status(thm)], ['154', '155', '156'])).
% 24.46/24.72  thf('158', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('159', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X3 @ 
% 24.46/24.72           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 24.46/24.72           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['157', '158'])).
% 24.46/24.72  thf('160', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k4_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['5', '6'])).
% 24.46/24.72  thf('161', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('162', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['160', '161'])).
% 24.46/24.72  thf('163', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X3 @ 
% 24.46/24.72           (k3_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))
% 24.46/24.72           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['159', '162'])).
% 24.46/24.72  thf('164', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('165', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['107', '108'])).
% 24.46/24.72  thf('166', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 24.46/24.72  thf('167', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['165', '166'])).
% 24.46/24.72  thf('168', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['164', '167'])).
% 24.46/24.72  thf('169', plain,
% 24.46/24.72      (![X9 : $i, X10 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 24.46/24.72           = (k3_xboole_0 @ X9 @ X10))),
% 24.46/24.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.46/24.72  thf('170', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 24.46/24.72           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['168', '169'])).
% 24.46/24.72  thf('171', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['65', '89'])).
% 24.46/24.72  thf('172', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.46/24.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 24.46/24.72  thf('173', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X1 @ X0)
% 24.46/24.72           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['170', '171', '172'])).
% 24.46/24.72  thf('174', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 24.46/24.72           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['163', '173'])).
% 24.46/24.72  thf('175', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 24.46/24.72           (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 24.46/24.72           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['151', '174'])).
% 24.46/24.72  thf('176', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 24.46/24.72           = (k3_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['163', '173'])).
% 24.46/24.72  thf('177', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['103', '114'])).
% 24.46/24.72  thf('178', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['175', '176', '177'])).
% 24.46/24.72  thf('179', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 24.46/24.72           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 24.46/24.72      inference('sup+', [status(thm)], ['150', '178'])).
% 24.46/24.72  thf('180', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 24.46/24.72           = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['141', '179'])).
% 24.46/24.72  thf('181', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['146', '149'])).
% 24.46/24.72  thf('182', plain,
% 24.46/24.72      (![X19 : $i, X20 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X19 @ X20)
% 24.46/24.72           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t98_xboole_1])).
% 24.46/24.72  thf('183', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['102', '121'])).
% 24.46/24.72  thf('184', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X1))),
% 24.46/24.72      inference('sup+', [status(thm)], ['182', '183'])).
% 24.46/24.72  thf('185', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['142', '143'])).
% 24.46/24.72  thf('186', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 24.46/24.72           = (X1))),
% 24.46/24.72      inference('demod', [status(thm)], ['184', '185'])).
% 24.46/24.72  thf('187', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['181', '186'])).
% 24.46/24.72  thf('188', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 24.46/24.72           (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))
% 24.46/24.72           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['180', '187'])).
% 24.46/24.72  thf('189', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['99', '100'])).
% 24.46/24.72  thf('190', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k1_xboole_0)
% 24.46/24.72           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['1', '54'])).
% 24.46/24.72  thf('191', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k1_xboole_0)
% 24.46/24.72           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))),
% 24.46/24.72      inference('sup+', [status(thm)], ['189', '190'])).
% 24.46/24.72  thf('192', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 24.46/24.72      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 24.46/24.72  thf('193', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X1 @ X0)
% 24.46/24.72           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['188', '191', '192'])).
% 24.46/24.72  thf('194', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['146', '149'])).
% 24.46/24.72  thf('195', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['128', '129'])).
% 24.46/24.72  thf('196', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ X0)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['194', '195'])).
% 24.46/24.72  thf('197', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['193', '196'])).
% 24.46/24.72  thf('198', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['142', '143'])).
% 24.46/24.72  thf('199', plain,
% 24.46/24.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 24.46/24.72           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 24.46/24.72      inference('cnf', [status(esa)], [t91_xboole_1])).
% 24.46/24.72  thf('200', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.46/24.72         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['198', '199'])).
% 24.46/24.72  thf('201', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['128', '129'])).
% 24.46/24.72  thf('202', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 24.46/24.72      inference('demod', [status(thm)], ['197', '200', '201'])).
% 24.46/24.72  thf('203', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['30', '31'])).
% 24.46/24.72  thf('204', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['99', '100'])).
% 24.46/24.72  thf('205', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k3_xboole_0 @ X0 @ X1)
% 24.46/24.72           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('sup+', [status(thm)], ['203', '204'])).
% 24.46/24.72  thf('206', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k3_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['202', '205'])).
% 24.46/24.72  thf('207', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['135', '136', '137'])).
% 24.46/24.72  thf('208', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ 
% 24.46/24.72           (k3_xboole_0 @ X1 @ X0)) = (k5_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['206', '207'])).
% 24.46/24.72  thf('209', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('sup+', [status(thm)], ['146', '149'])).
% 24.46/24.72  thf('210', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k2_xboole_0 @ X1 @ X0)
% 24.46/24.72           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 24.46/24.72      inference('demod', [status(thm)], ['188', '191', '192'])).
% 24.46/24.72  thf('211', plain,
% 24.46/24.72      (![X0 : $i, X1 : $i]:
% 24.46/24.72         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 24.46/24.72           = (k5_xboole_0 @ X1 @ X0))),
% 24.46/24.72      inference('demod', [status(thm)], ['208', '209', '210'])).
% 24.46/24.72  thf('212', plain,
% 24.46/24.72      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 24.46/24.72      inference('demod', [status(thm)], ['0', '211'])).
% 24.46/24.72  thf('213', plain, ($false), inference('simplify', [status(thm)], ['212'])).
% 24.46/24.72  
% 24.46/24.72  % SZS output end Refutation
% 24.46/24.72  
% 24.46/24.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
