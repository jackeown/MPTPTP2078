%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w30VL50YMj

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 781 expanded)
%              Number of leaves         :   18 ( 273 expanded)
%              Depth                    :   21
%              Number of atoms          : 1089 (6250 expanded)
%              Number of equality atoms :  114 ( 734 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25','26','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['38','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ) )
    = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77','78','83'])).

thf('85',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['76','77','78','83'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['69','84','85','86'])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) @ sk_A )
    = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['87','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['69','84','85','86'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('103',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101','102'])).

thf('104',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('105',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('107',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','53'])).

thf('110',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','112'])).

thf('114',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['107','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.w30VL50YMj
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:45:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.50/3.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.50/3.71  % Solved by: fo/fo7.sh
% 3.50/3.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.50/3.71  % done 4432 iterations in 3.257s
% 3.50/3.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.50/3.71  % SZS output start Refutation
% 3.50/3.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.50/3.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.50/3.71  thf(sk_B_type, type, sk_B: $i).
% 3.50/3.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.50/3.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.50/3.71  thf(sk_C_type, type, sk_C: $i).
% 3.50/3.71  thf(sk_A_type, type, sk_A: $i).
% 3.50/3.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.50/3.71  thf(t81_xboole_1, conjecture,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.50/3.71       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 3.50/3.71  thf(zf_stmt_0, negated_conjecture,
% 3.50/3.71    (~( ![A:$i,B:$i,C:$i]:
% 3.50/3.71        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.50/3.71          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 3.50/3.71    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 3.50/3.71  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(t39_xboole_1, axiom,
% 3.50/3.71    (![A:$i,B:$i]:
% 3.50/3.71     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.50/3.71  thf('1', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf(d7_xboole_0, axiom,
% 3.50/3.71    (![A:$i,B:$i]:
% 3.50/3.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.50/3.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.50/3.71  thf('3', plain,
% 3.50/3.71      (![X2 : $i, X3 : $i]:
% 3.50/3.71         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.50/3.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.50/3.71  thf('4', plain,
% 3.50/3.71      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['2', '3'])).
% 3.50/3.71  thf(t47_xboole_1, axiom,
% 3.50/3.71    (![A:$i,B:$i]:
% 3.50/3.71     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.50/3.71  thf('5', plain,
% 3.50/3.71      (![X12 : $i, X13 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 3.50/3.71           = (k4_xboole_0 @ X12 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.50/3.71  thf('6', plain,
% 3.50/3.71      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 3.50/3.71         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['4', '5'])).
% 3.50/3.71  thf(t3_boole, axiom,
% 3.50/3.71    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.50/3.71  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('8', plain,
% 3.50/3.71      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 3.50/3.71      inference('demod', [status(thm)], ['6', '7'])).
% 3.50/3.71  thf('9', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf(t48_xboole_1, axiom,
% 3.50/3.71    (![A:$i,B:$i]:
% 3.50/3.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.50/3.71  thf('10', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('11', plain,
% 3.50/3.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['9', '10'])).
% 3.50/3.71  thf(t2_boole, axiom,
% 3.50/3.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.50/3.71  thf('12', plain,
% 3.50/3.71      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.50/3.71      inference('cnf', [status(esa)], [t2_boole])).
% 3.50/3.71  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['11', '12'])).
% 3.50/3.71  thf(t41_xboole_1, axiom,
% 3.50/3.71    (![A:$i,B:$i,C:$i]:
% 3.50/3.71     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.50/3.71       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.50/3.71  thf('14', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('15', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('16', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.50/3.71           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['14', '15'])).
% 3.50/3.71  thf('17', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 3.50/3.71           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['13', '16'])).
% 3.50/3.71  thf('18', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('19', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('20', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 3.50/3.71           = (k4_xboole_0 @ X1 @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['18', '19'])).
% 3.50/3.71  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['11', '12'])).
% 3.50/3.71  thf('22', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['20', '21'])).
% 3.50/3.71  thf('23', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('24', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.50/3.71           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['22', '23'])).
% 3.50/3.71  thf('25', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf(commutativity_k3_xboole_0, axiom,
% 3.50/3.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.50/3.71  thf('26', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['11', '12'])).
% 3.50/3.71  thf('28', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('29', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['27', '28'])).
% 3.50/3.71  thf(t4_boole, axiom,
% 3.50/3.71    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 3.50/3.71  thf('30', plain,
% 3.50/3.71      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 3.50/3.71      inference('cnf', [status(esa)], [t4_boole])).
% 3.50/3.71  thf('31', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['29', '30'])).
% 3.50/3.71  thf('32', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('33', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 3.50/3.71           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['31', '32'])).
% 3.50/3.71  thf('34', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('35', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['33', '34'])).
% 3.50/3.71  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['24', '25', '26', '35'])).
% 3.50/3.71  thf('37', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((X1)
% 3.50/3.71           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['17', '36'])).
% 3.50/3.71  thf('38', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('39', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 3.50/3.71           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['14', '15'])).
% 3.50/3.71  thf('40', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('41', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('42', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X2 @ 
% 3.50/3.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 3.50/3.71      inference('sup+', [status(thm)], ['40', '41'])).
% 3.50/3.71  thf('43', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('44', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X2 @ 
% 3.50/3.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 3.50/3.71      inference('demod', [status(thm)], ['42', '43'])).
% 3.50/3.71  thf('45', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.50/3.71      inference('sup+', [status(thm)], ['39', '44'])).
% 3.50/3.71  thf('46', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('47', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('48', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 3.50/3.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 3.50/3.71      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.50/3.71  thf('49', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['11', '12'])).
% 3.50/3.71  thf('51', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 3.50/3.71           = (k1_xboole_0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['49', '50'])).
% 3.50/3.71  thf('52', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('53', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['51', '52'])).
% 3.50/3.71  thf('54', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['48', '53'])).
% 3.50/3.71  thf('55', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('56', plain,
% 3.50/3.71      (![X2 : $i, X4 : $i]:
% 3.50/3.71         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.50/3.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.50/3.71  thf('57', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('sup-', [status(thm)], ['55', '56'])).
% 3.50/3.71  thf('58', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         (((k1_xboole_0) != (k1_xboole_0))
% 3.50/3.71          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['54', '57'])).
% 3.50/3.71  thf('59', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 3.50/3.71      inference('simplify', [status(thm)], ['58'])).
% 3.50/3.71  thf('60', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 3.50/3.71      inference('sup+', [status(thm)], ['38', '59'])).
% 3.50/3.71  thf('61', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 3.50/3.71          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 3.50/3.71      inference('sup+', [status(thm)], ['37', '60'])).
% 3.50/3.71  thf('62', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (r1_xboole_0 @ sk_A @ 
% 3.50/3.71          (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)) @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['8', '61'])).
% 3.50/3.71  thf('63', plain,
% 3.50/3.71      ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C))),
% 3.50/3.71      inference('sup+', [status(thm)], ['1', '62'])).
% 3.50/3.71  thf('64', plain,
% 3.50/3.71      (![X2 : $i, X3 : $i]:
% 3.50/3.71         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.50/3.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.50/3.71  thf('65', plain,
% 3.50/3.71      (((k3_xboole_0 @ sk_A @ 
% 3.50/3.71         (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)) = (k1_xboole_0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['63', '64'])).
% 3.50/3.71  thf('66', plain,
% 3.50/3.71      (![X12 : $i, X13 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 3.50/3.71           = (k4_xboole_0 @ X12 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.50/3.71  thf('67', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('68', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 3.50/3.71           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 3.50/3.71      inference('sup+', [status(thm)], ['66', '67'])).
% 3.50/3.71  thf('69', plain,
% 3.50/3.71      (((k2_xboole_0 @ k1_xboole_0 @ 
% 3.50/3.71         (k4_xboole_0 @ sk_A @ 
% 3.50/3.71          (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)))
% 3.50/3.71         = (k2_xboole_0 @ 
% 3.50/3.71            (k3_xboole_0 @ sk_A @ 
% 3.50/3.71             (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)) @ 
% 3.50/3.71            sk_A))),
% 3.50/3.71      inference('sup+', [status(thm)], ['65', '68'])).
% 3.50/3.71  thf('70', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('71', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('72', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X0 @ X1)
% 3.50/3.71           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['70', '71'])).
% 3.50/3.71  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['11', '12'])).
% 3.50/3.71  thf('74', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['72', '73'])).
% 3.50/3.71  thf('75', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('76', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 3.50/3.71           = (k3_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 3.50/3.71      inference('sup+', [status(thm)], ['74', '75'])).
% 3.50/3.71  thf('77', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('78', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('79', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['51', '52'])).
% 3.50/3.71  thf('80', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('81', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 3.50/3.71           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['79', '80'])).
% 3.50/3.71  thf('82', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 3.50/3.71      inference('cnf', [status(esa)], [t3_boole])).
% 3.50/3.71  thf('83', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['81', '82'])).
% 3.50/3.71  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['76', '77', '78', '83'])).
% 3.50/3.71  thf('85', plain,
% 3.50/3.71      (((k3_xboole_0 @ sk_A @ 
% 3.50/3.71         (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)) = (k1_xboole_0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['63', '64'])).
% 3.50/3.71  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['76', '77', '78', '83'])).
% 3.50/3.71  thf('87', plain,
% 3.50/3.71      (((k4_xboole_0 @ sk_A @ 
% 3.50/3.71         (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)) = (sk_A))),
% 3.50/3.71      inference('demod', [status(thm)], ['69', '84', '85', '86'])).
% 3.50/3.71  thf('88', plain,
% 3.50/3.71      (![X14 : $i, X15 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 3.50/3.71           = (k3_xboole_0 @ X14 @ X15))),
% 3.50/3.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.50/3.71  thf('89', plain,
% 3.50/3.71      (![X6 : $i, X7 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 3.50/3.71           = (k2_xboole_0 @ X6 @ X7))),
% 3.50/3.71      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.50/3.71  thf('90', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 3.50/3.71           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 3.50/3.71      inference('sup+', [status(thm)], ['88', '89'])).
% 3.50/3.71  thf('91', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X2 @ 
% 3.50/3.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 3.50/3.71      inference('demod', [status(thm)], ['42', '43'])).
% 3.50/3.71  thf('92', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 3.50/3.71           (k3_xboole_0 @ X0 @ X1))
% 3.50/3.71           = (k4_xboole_0 @ X2 @ 
% 3.50/3.71              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 3.50/3.71               (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))))),
% 3.50/3.71      inference('sup+', [status(thm)], ['90', '91'])).
% 3.50/3.71  thf('93', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('94', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 3.50/3.71           = (k4_xboole_0 @ X2 @ 
% 3.50/3.71              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 3.50/3.71      inference('demod', [status(thm)], ['42', '43'])).
% 3.50/3.71  thf('95', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('96', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 3.50/3.71           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 3.50/3.71           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 3.50/3.71      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 3.50/3.71  thf('97', plain,
% 3.50/3.71      (((k3_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C) @ 
% 3.50/3.71         sk_A)
% 3.50/3.71         = (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ 
% 3.50/3.71            (k4_xboole_0 @ sk_A @ 
% 3.50/3.71             (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C))))),
% 3.50/3.71      inference('sup+', [status(thm)], ['87', '96'])).
% 3.50/3.71  thf('98', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('99', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('demod', [status(thm)], ['33', '34'])).
% 3.50/3.71  thf('100', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('101', plain,
% 3.50/3.71      (((k4_xboole_0 @ sk_A @ 
% 3.50/3.71         (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_C)) = (sk_A))),
% 3.50/3.71      inference('demod', [status(thm)], ['69', '84', '85', '86'])).
% 3.50/3.71  thf('102', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.50/3.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.50/3.71  thf('103', plain,
% 3.50/3.71      (((k3_xboole_0 @ sk_A @ sk_C)
% 3.50/3.71         = (k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 3.50/3.71      inference('demod', [status(thm)], ['97', '98', '99', '100', '101', '102'])).
% 3.50/3.71  thf('104', plain,
% 3.50/3.71      (![X12 : $i, X13 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 3.50/3.71           = (k4_xboole_0 @ X12 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.50/3.71  thf('105', plain,
% 3.50/3.71      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_C))
% 3.50/3.71         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['103', '104'])).
% 3.50/3.71  thf('106', plain,
% 3.50/3.71      (![X12 : $i, X13 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 3.50/3.71           = (k4_xboole_0 @ X12 @ X13))),
% 3.50/3.71      inference('cnf', [status(esa)], [t47_xboole_1])).
% 3.50/3.71  thf('107', plain,
% 3.50/3.71      (((k4_xboole_0 @ sk_A @ sk_C)
% 3.50/3.71         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 3.50/3.71      inference('demod', [status(thm)], ['105', '106'])).
% 3.50/3.71  thf('108', plain,
% 3.50/3.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.50/3.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 3.50/3.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 3.50/3.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.50/3.71  thf('109', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.50/3.71      inference('demod', [status(thm)], ['48', '53'])).
% 3.50/3.71  thf('110', plain,
% 3.50/3.71      (![X2 : $i, X4 : $i]:
% 3.50/3.71         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.50/3.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.50/3.71  thf('111', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]:
% 3.50/3.71         (((k1_xboole_0) != (k1_xboole_0))
% 3.50/3.71          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['109', '110'])).
% 3.50/3.71  thf('112', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 3.50/3.71      inference('simplify', [status(thm)], ['111'])).
% 3.50/3.71  thf('113', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.50/3.71      inference('sup+', [status(thm)], ['108', '112'])).
% 3.50/3.71  thf('114', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 3.50/3.71      inference('sup+', [status(thm)], ['107', '113'])).
% 3.50/3.71  thf('115', plain, ($false), inference('demod', [status(thm)], ['0', '114'])).
% 3.50/3.71  
% 3.50/3.71  % SZS output end Refutation
% 3.50/3.71  
% 3.50/3.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
