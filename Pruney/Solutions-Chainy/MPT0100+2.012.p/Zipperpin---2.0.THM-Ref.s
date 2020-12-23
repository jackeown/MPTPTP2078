%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ln94F0cdbK

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:54 EST 2020

% Result     : Theorem 15.72s
% Output     : Refutation 15.72s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 609 expanded)
%              Number of leaves         :   18 ( 214 expanded)
%              Depth                    :   23
%              Number of atoms          : 1305 (4922 expanded)
%              Number of equality atoms :  136 ( 601 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t93_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t55_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','10','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('79',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['72','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('93',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['81','82','83','103','108','109'])).

thf('111',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('123',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','122'])).

thf('124',plain,(
    $false ),
    inference(simplify,[status(thm)],['123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ln94F0cdbK
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.72/15.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.72/15.96  % Solved by: fo/fo7.sh
% 15.72/15.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.72/15.96  % done 8507 iterations in 15.495s
% 15.72/15.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.72/15.96  % SZS output start Refutation
% 15.72/15.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.72/15.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.72/15.96  thf(sk_B_type, type, sk_B: $i).
% 15.72/15.96  thf(sk_A_type, type, sk_A: $i).
% 15.72/15.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.72/15.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 15.72/15.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.72/15.96  thf(t93_xboole_1, conjecture,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k2_xboole_0 @ A @ B ) =
% 15.72/15.96       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.72/15.96  thf(zf_stmt_0, negated_conjecture,
% 15.72/15.96    (~( ![A:$i,B:$i]:
% 15.72/15.96        ( ( k2_xboole_0 @ A @ B ) =
% 15.72/15.96          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 15.72/15.96    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 15.72/15.96  thf('0', plain,
% 15.72/15.96      (((k2_xboole_0 @ sk_A @ sk_B)
% 15.72/15.96         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 15.72/15.96             (k3_xboole_0 @ sk_A @ sk_B)))),
% 15.72/15.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.72/15.96  thf(t55_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 15.72/15.96       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 15.72/15.96  thf('1', plain,
% 15.72/15.96      (![X17 : $i, X18 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ (k3_xboole_0 @ X17 @ X18))
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ 
% 15.72/15.96              (k4_xboole_0 @ X18 @ X17)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t55_xboole_1])).
% 15.72/15.96  thf(d6_xboole_0, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k5_xboole_0 @ A @ B ) =
% 15.72/15.96       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 15.72/15.96  thf('2', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('3', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X1 @ X0)
% 15.72/15.96           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['1', '2'])).
% 15.72/15.96  thf('4', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('5', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 15.72/15.96              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['3', '4'])).
% 15.72/15.96  thf('6', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf(commutativity_k2_xboole_0, axiom,
% 15.72/15.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 15.72/15.96  thf('7', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('8', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['6', '7'])).
% 15.72/15.96  thf('9', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('10', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['8', '9'])).
% 15.72/15.96  thf(t51_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 15.72/15.96       ( A ) ))).
% 15.72/15.96  thf('11', plain,
% 15.72/15.96      (![X15 : $i, X16 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.72/15.96           = (X15))),
% 15.72/15.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.72/15.96  thf('12', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf(t41_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i,C:$i]:
% 15.72/15.96     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 15.72/15.96       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.72/15.96  thf('13', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf(t3_boole, axiom,
% 15.72/15.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 15.72/15.96  thf('14', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 15.72/15.96      inference('cnf', [status(esa)], [t3_boole])).
% 15.72/15.96  thf(t48_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.72/15.96  thf('15', plain,
% 15.72/15.96      (![X13 : $i, X14 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.72/15.96           = (k3_xboole_0 @ X13 @ X14))),
% 15.72/15.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.72/15.96  thf('16', plain,
% 15.72/15.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['14', '15'])).
% 15.72/15.96  thf(t2_boole, axiom,
% 15.72/15.96    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 15.72/15.96  thf('17', plain,
% 15.72/15.96      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 15.72/15.96      inference('cnf', [status(esa)], [t2_boole])).
% 15.72/15.96  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['16', '17'])).
% 15.72/15.96  thf('19', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 15.72/15.96           = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['13', '18'])).
% 15.72/15.96  thf(t39_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 15.72/15.96  thf('20', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('21', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['19', '20'])).
% 15.72/15.96  thf('22', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['12', '21'])).
% 15.72/15.96  thf('23', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['11', '22'])).
% 15.72/15.96  thf('24', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('25', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 15.72/15.96           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['23', '24'])).
% 15.72/15.96  thf('26', plain,
% 15.72/15.96      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 15.72/15.96      inference('cnf', [status(esa)], [t2_boole])).
% 15.72/15.96  thf('27', plain,
% 15.72/15.96      (![X15 : $i, X16 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.72/15.96           = (X15))),
% 15.72/15.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.72/15.96  thf('28', plain,
% 15.72/15.96      (![X0 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['26', '27'])).
% 15.72/15.96  thf('29', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 15.72/15.96      inference('cnf', [status(esa)], [t3_boole])).
% 15.72/15.96  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['28', '29'])).
% 15.72/15.96  thf('31', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['30', '31'])).
% 15.72/15.96  thf('33', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf(t40_xboole_1, axiom,
% 15.72/15.96    (![A:$i,B:$i]:
% 15.72/15.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 15.72/15.96  thf('34', plain,
% 15.72/15.96      (![X8 : $i, X9 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 15.72/15.96           = (k4_xboole_0 @ X8 @ X9))),
% 15.72/15.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 15.72/15.96  thf('35', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 15.72/15.96           = (k4_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('sup+', [status(thm)], ['33', '34'])).
% 15.72/15.96  thf('36', plain,
% 15.72/15.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['32', '35'])).
% 15.72/15.96  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['16', '17'])).
% 15.72/15.96  thf('38', plain,
% 15.72/15.96      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['36', '37'])).
% 15.72/15.96  thf('39', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k1_xboole_0)
% 15.72/15.96           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['25', '38'])).
% 15.72/15.96  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['30', '31'])).
% 15.72/15.96  thf('41', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['5', '10', '39', '40'])).
% 15.72/15.96  thf('42', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X1 @ X0)
% 15.72/15.96           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['1', '2'])).
% 15.72/15.96  thf('43', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('44', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('45', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 15.72/15.96           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['43', '44'])).
% 15.72/15.96  thf('46', plain,
% 15.72/15.96      (![X13 : $i, X14 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.72/15.96           = (k3_xboole_0 @ X13 @ X14))),
% 15.72/15.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.72/15.96  thf('47', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('48', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 15.72/15.96           = (k4_xboole_0 @ X2 @ 
% 15.72/15.96              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['46', '47'])).
% 15.72/15.96  thf('49', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('50', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 15.72/15.96           = (k4_xboole_0 @ X2 @ 
% 15.72/15.96              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 15.72/15.96      inference('demod', [status(thm)], ['48', '49'])).
% 15.72/15.96  thf('51', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 15.72/15.96           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['45', '50'])).
% 15.72/15.96  thf('52', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('53', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('54', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['19', '20'])).
% 15.72/15.96  thf('55', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('56', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 15.72/15.96           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['54', '55'])).
% 15.72/15.96  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['30', '31'])).
% 15.72/15.96  thf('58', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('59', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ X0)
% 15.72/15.96           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['56', '57', '58'])).
% 15.72/15.96  thf('60', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X0 @ X1)
% 15.72/15.96           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['53', '59'])).
% 15.72/15.96  thf('61', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 15.72/15.96           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['52', '60'])).
% 15.72/15.96  thf('62', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('63', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X0 @ X1)
% 15.72/15.96           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['53', '59'])).
% 15.72/15.96  thf('64', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 15.72/15.96           = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('demod', [status(thm)], ['61', '62', '63'])).
% 15.72/15.96  thf('65', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 15.72/15.96           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['51', '64'])).
% 15.72/15.96  thf('66', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['12', '21'])).
% 15.72/15.96  thf('67', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['65', '66'])).
% 15.72/15.96  thf('68', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['42', '67'])).
% 15.72/15.96  thf('69', plain,
% 15.72/15.96      (![X15 : $i, X16 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.72/15.96           = (X15))),
% 15.72/15.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.72/15.96  thf('70', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ k1_xboole_0 @ 
% 15.72/15.96           (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['68', '69'])).
% 15.72/15.96  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['28', '29'])).
% 15.72/15.96  thf('72', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['70', '71'])).
% 15.72/15.96  thf('73', plain,
% 15.72/15.96      (![X15 : $i, X16 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.72/15.96           = (X15))),
% 15.72/15.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.72/15.96  thf('74', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('75', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('76', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 15.72/15.96              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['74', '75'])).
% 15.72/15.96  thf('77', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 15.72/15.96           (k4_xboole_0 @ X0 @ X1))
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 15.72/15.96              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 15.72/15.96               (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['73', '76'])).
% 15.72/15.96  thf('78', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['8', '9'])).
% 15.72/15.96  thf('79', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('80', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 15.72/15.96           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)))
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 15.72/15.96              (k4_xboole_0 @ X0 @ 
% 15.72/15.96               (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))))))),
% 15.72/15.96      inference('demod', [status(thm)], ['77', '78', '79'])).
% 15.72/15.96  thf('81', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 15.72/15.96           (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ 
% 15.72/15.96              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))))),
% 15.72/15.96      inference('sup+', [status(thm)], ['72', '80'])).
% 15.72/15.96  thf('82', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['70', '71'])).
% 15.72/15.96  thf('83', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['8', '9'])).
% 15.72/15.96  thf('84', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['6', '7'])).
% 15.72/15.96  thf('85', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['19', '20'])).
% 15.72/15.96  thf('86', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('87', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ k1_xboole_0 @ 
% 15.72/15.96              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['85', '86'])).
% 15.72/15.96  thf('88', plain,
% 15.72/15.96      (![X8 : $i, X9 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 15.72/15.96           = (k4_xboole_0 @ X8 @ X9))),
% 15.72/15.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 15.72/15.96  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['28', '29'])).
% 15.72/15.96  thf('90', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k4_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['87', '88', '89'])).
% 15.72/15.96  thf('91', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['84', '90'])).
% 15.72/15.96  thf('92', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['8', '9'])).
% 15.72/15.96  thf('93', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('94', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 15.72/15.96      inference('demod', [status(thm)], ['91', '92', '93'])).
% 15.72/15.96  thf('95', plain,
% 15.72/15.96      (![X13 : $i, X14 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.72/15.96           = (k3_xboole_0 @ X13 @ X14))),
% 15.72/15.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.72/15.96  thf('96', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('97', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 15.72/15.96      inference('sup+', [status(thm)], ['95', '96'])).
% 15.72/15.96  thf('98', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('99', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('100', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['97', '98', '99'])).
% 15.72/15.96  thf('101', plain,
% 15.72/15.96      (![X15 : $i, X16 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.72/15.96           = (X15))),
% 15.72/15.96      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.72/15.96  thf('102', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 15.72/15.96      inference('sup+', [status(thm)], ['100', '101'])).
% 15.72/15.96  thf('103', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k4_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('demod', [status(thm)], ['94', '102'])).
% 15.72/15.96  thf('104', plain,
% 15.72/15.96      (![X2 : $i, X3 : $i]:
% 15.72/15.96         ((k5_xboole_0 @ X2 @ X3)
% 15.72/15.96           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 15.72/15.96      inference('cnf', [status(esa)], [d6_xboole_0])).
% 15.72/15.96  thf('105', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['12', '21'])).
% 15.72/15.96  thf('106', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k1_xboole_0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['104', '105'])).
% 15.72/15.96  thf('107', plain,
% 15.72/15.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 15.72/15.96           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 15.72/15.96      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.72/15.96  thf('108', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 15.72/15.96           = (k1_xboole_0))),
% 15.72/15.96      inference('demod', [status(thm)], ['106', '107'])).
% 15.72/15.96  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['30', '31'])).
% 15.72/15.96  thf('110', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k4_xboole_0 @ X0 @ X1)
% 15.72/15.96           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 15.72/15.96      inference('demod', [status(thm)], ['81', '82', '83', '103', '108', '109'])).
% 15.72/15.96  thf('111', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('112', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['110', '111'])).
% 15.72/15.96  thf('113', plain,
% 15.72/15.96      (![X5 : $i, X6 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 15.72/15.96           = (k2_xboole_0 @ X5 @ X6))),
% 15.72/15.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.72/15.96  thf('114', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['112', '113'])).
% 15.72/15.96  thf('115', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['41', '114'])).
% 15.72/15.96  thf('116', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.72/15.96  thf('117', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k1_xboole_0)
% 15.72/15.96           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['25', '38'])).
% 15.72/15.96  thf('118', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 15.72/15.96           = (k2_xboole_0 @ X0 @ X1))),
% 15.72/15.96      inference('demod', [status(thm)], ['61', '62', '63'])).
% 15.72/15.96  thf('119', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 15.72/15.96           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('sup+', [status(thm)], ['117', '118'])).
% 15.72/15.96  thf('120', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 15.72/15.96      inference('sup+', [status(thm)], ['30', '31'])).
% 15.72/15.96  thf('121', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ X1 @ X0)
% 15.72/15.96           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.72/15.96      inference('demod', [status(thm)], ['119', '120'])).
% 15.72/15.96  thf('122', plain,
% 15.72/15.96      (![X0 : $i, X1 : $i]:
% 15.72/15.96         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.72/15.96           = (k2_xboole_0 @ X1 @ X0))),
% 15.72/15.96      inference('demod', [status(thm)], ['115', '116', '121'])).
% 15.72/15.96  thf('123', plain,
% 15.72/15.96      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 15.72/15.96      inference('demod', [status(thm)], ['0', '122'])).
% 15.72/15.96  thf('124', plain, ($false), inference('simplify', [status(thm)], ['123'])).
% 15.72/15.96  
% 15.72/15.96  % SZS output end Refutation
% 15.72/15.96  
% 15.72/15.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
