%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WX3nqayAQs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:58 EST 2020

% Result     : Theorem 4.35s
% Output     : Refutation 4.35s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 440 expanded)
%              Number of leaves         :   15 ( 167 expanded)
%              Depth                    :   21
%              Number of atoms          :  953 (3960 expanded)
%              Number of equality atoms :  100 ( 433 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t94_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','12','13','14','15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','54'])).

thf('56',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('57',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('71',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k2_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('81',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('89',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','87','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WX3nqayAQs
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.35/4.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.35/4.54  % Solved by: fo/fo7.sh
% 4.35/4.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.35/4.54  % done 1667 iterations in 4.076s
% 4.35/4.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.35/4.54  % SZS output start Refutation
% 4.35/4.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.35/4.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.35/4.54  thf(sk_B_type, type, sk_B: $i).
% 4.35/4.54  thf(sk_A_type, type, sk_A: $i).
% 4.35/4.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.35/4.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.35/4.54  thf(t94_xboole_1, conjecture,
% 4.35/4.54    (![A:$i,B:$i]:
% 4.35/4.54     ( ( k2_xboole_0 @ A @ B ) =
% 4.35/4.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.35/4.54  thf(zf_stmt_0, negated_conjecture,
% 4.35/4.54    (~( ![A:$i,B:$i]:
% 4.35/4.54        ( ( k2_xboole_0 @ A @ B ) =
% 4.35/4.54          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 4.35/4.54    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 4.35/4.54  thf('0', plain,
% 4.35/4.54      (((k2_xboole_0 @ sk_A @ sk_B)
% 4.35/4.54         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 4.35/4.54             (k3_xboole_0 @ sk_A @ sk_B)))),
% 4.35/4.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.35/4.54  thf(d6_xboole_0, axiom,
% 4.35/4.54    (![A:$i,B:$i]:
% 4.35/4.54     ( ( k5_xboole_0 @ A @ B ) =
% 4.35/4.54       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 4.35/4.54  thf('1', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf(commutativity_k2_xboole_0, axiom,
% 4.35/4.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.35/4.54  thf('2', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('3', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k5_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['1', '2'])).
% 4.35/4.54  thf('4', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf('5', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['3', '4'])).
% 4.35/4.54  thf(t48_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i]:
% 4.35/4.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.35/4.54  thf('6', plain,
% 4.35/4.54      (![X9 : $i, X10 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.35/4.54           = (k3_xboole_0 @ X9 @ X10))),
% 4.35/4.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.35/4.54  thf('7', plain,
% 4.35/4.54      (![X9 : $i, X10 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.35/4.54           = (k3_xboole_0 @ X9 @ X10))),
% 4.35/4.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.35/4.54  thf('8', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['6', '7'])).
% 4.35/4.54  thf('9', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['6', '7'])).
% 4.35/4.54  thf(t51_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i]:
% 4.35/4.54     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 4.35/4.54       ( A ) ))).
% 4.35/4.54  thf('10', plain,
% 4.35/4.54      (![X14 : $i, X15 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 4.35/4.54           = (X14))),
% 4.35/4.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.35/4.54  thf('11', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 4.35/4.54           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['9', '10'])).
% 4.35/4.54  thf('12', plain,
% 4.35/4.54      (![X9 : $i, X10 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.35/4.54           = (k3_xboole_0 @ X9 @ X10))),
% 4.35/4.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.35/4.54  thf('13', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf(t39_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i]:
% 4.35/4.54     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.35/4.54  thf('14', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('15', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('16', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 4.35/4.54  thf('17', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 4.35/4.54           = (X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['8', '16'])).
% 4.35/4.54  thf('18', plain,
% 4.35/4.54      (![X14 : $i, X15 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 4.35/4.54           = (X14))),
% 4.35/4.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.35/4.54  thf('19', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 4.35/4.54  thf(t4_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i,C:$i]:
% 4.35/4.54     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.35/4.54       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.35/4.54  thf('20', plain,
% 4.35/4.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 4.35/4.54           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.35/4.54  thf('21', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ X1)
% 4.35/4.54           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['19', '20'])).
% 4.35/4.54  thf('22', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['18', '21'])).
% 4.35/4.54  thf('23', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ X1) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['17', '22'])).
% 4.35/4.54  thf('24', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf('25', plain,
% 4.35/4.54      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['23', '24'])).
% 4.35/4.54  thf('26', plain,
% 4.35/4.54      (![X9 : $i, X10 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.35/4.54           = (k3_xboole_0 @ X9 @ X10))),
% 4.35/4.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.35/4.54  thf('27', plain,
% 4.35/4.54      (![X0 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 4.35/4.54           = (k3_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['25', '26'])).
% 4.35/4.54  thf('28', plain,
% 4.35/4.54      (![X14 : $i, X15 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 4.35/4.54           = (X14))),
% 4.35/4.54      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.35/4.54  thf('29', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ X1) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['17', '22'])).
% 4.35/4.54  thf('30', plain,
% 4.35/4.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 4.35/4.54           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.35/4.54  thf('31', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('32', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['30', '31'])).
% 4.35/4.54  thf('33', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ X0)
% 4.35/4.54           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['29', '32'])).
% 4.35/4.54  thf('34', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['28', '33'])).
% 4.35/4.54  thf(t52_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i,C:$i]:
% 4.35/4.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.35/4.54       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 4.35/4.54  thf('35', plain,
% 4.35/4.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 4.35/4.54              (k3_xboole_0 @ X16 @ X18)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 4.35/4.54  thf('36', plain,
% 4.35/4.54      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['23', '24'])).
% 4.35/4.54  thf('37', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('38', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['11', '12', '13', '14', '15'])).
% 4.35/4.54  thf('39', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)) = (X0))),
% 4.35/4.54      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 4.35/4.54  thf('40', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('demod', [status(thm)], ['27', '39'])).
% 4.35/4.54  thf('41', plain,
% 4.35/4.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 4.35/4.54              (k3_xboole_0 @ X16 @ X18)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t52_xboole_1])).
% 4.35/4.54  thf('42', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['40', '41'])).
% 4.35/4.54  thf('43', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('44', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.35/4.54      inference('demod', [status(thm)], ['42', '43'])).
% 4.35/4.54  thf('45', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['18', '21'])).
% 4.35/4.54  thf('46', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ X1) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['17', '22'])).
% 4.35/4.54  thf('47', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 4.35/4.54      inference('demod', [status(thm)], ['45', '46'])).
% 4.35/4.54  thf('48', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['44', '47'])).
% 4.35/4.54  thf('49', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf(t41_xboole_1, axiom,
% 4.35/4.54    (![A:$i,B:$i,C:$i]:
% 4.35/4.54     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 4.35/4.54       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.35/4.54  thf('50', plain,
% 4.35/4.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 4.35/4.54           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.35/4.54  thf('51', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 4.35/4.54           (k4_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['49', '50'])).
% 4.35/4.54  thf('52', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['48', '51'])).
% 4.35/4.54  thf('53', plain,
% 4.35/4.54      (![X9 : $i, X10 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 4.35/4.54           = (k3_xboole_0 @ X9 @ X10))),
% 4.35/4.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.35/4.54  thf('54', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k3_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['52', '53'])).
% 4.35/4.54  thf('55', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k3_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['5', '54'])).
% 4.35/4.54  thf('56', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ X1) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['17', '22'])).
% 4.35/4.54  thf('57', plain,
% 4.35/4.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 4.35/4.54           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.35/4.54  thf('58', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.35/4.54           = (k4_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['56', '57'])).
% 4.35/4.54  thf('59', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf('60', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 4.35/4.54              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 4.35/4.54      inference('sup+', [status(thm)], ['58', '59'])).
% 4.35/4.54  thf('61', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('62', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('63', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.35/4.54           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('demod', [status(thm)], ['60', '61', '62'])).
% 4.35/4.54  thf('64', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['3', '4'])).
% 4.35/4.54  thf('65', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('demod', [status(thm)], ['63', '64'])).
% 4.35/4.54  thf('66', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('67', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['65', '66'])).
% 4.35/4.54  thf('68', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['55', '67'])).
% 4.35/4.54  thf('69', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('70', plain,
% 4.35/4.54      (![X2 : $i, X3 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ X2 @ X3)
% 4.35/4.54           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 4.35/4.54      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.35/4.54  thf('71', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('72', plain,
% 4.35/4.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 4.35/4.54           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.35/4.54  thf('73', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 4.35/4.54           = (k2_xboole_0 @ X2 @ 
% 4.35/4.54              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))))),
% 4.35/4.54      inference('sup+', [status(thm)], ['71', '72'])).
% 4.35/4.54  thf('74', plain,
% 4.35/4.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X13)
% 4.35/4.54           = (k2_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.35/4.54  thf('75', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X2 @ 
% 4.35/4.54              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))))),
% 4.35/4.54      inference('demod', [status(thm)], ['73', '74'])).
% 4.35/4.54  thf('76', plain,
% 4.35/4.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.35/4.54         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 4.35/4.54           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 4.35/4.54      inference('cnf', [status(esa)], [t41_xboole_1])).
% 4.35/4.54  thf('77', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('78', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))))),
% 4.35/4.54      inference('demod', [status(thm)], ['75', '76', '77'])).
% 4.35/4.54  thf('79', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['70', '78'])).
% 4.35/4.54  thf('80', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('81', plain,
% 4.35/4.54      (![X4 : $i, X5 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 4.35/4.54           = (k2_xboole_0 @ X4 @ X5))),
% 4.35/4.54      inference('cnf', [status(esa)], [t39_xboole_1])).
% 4.35/4.54  thf('82', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 4.35/4.54  thf('83', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ X1) = (X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['17', '22'])).
% 4.35/4.54  thf('84', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 4.35/4.54           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.35/4.54      inference('sup+', [status(thm)], ['30', '31'])).
% 4.35/4.54  thf('85', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X1 @ X0))),
% 4.35/4.54      inference('sup+', [status(thm)], ['83', '84'])).
% 4.35/4.54  thf('86', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('sup+', [status(thm)], ['82', '85'])).
% 4.35/4.54  thf('87', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]:
% 4.35/4.54         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.35/4.54           = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('demod', [status(thm)], ['68', '69', '86'])).
% 4.35/4.54  thf('88', plain,
% 4.35/4.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.35/4.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.35/4.54  thf('89', plain,
% 4.35/4.54      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 4.35/4.54      inference('demod', [status(thm)], ['0', '87', '88'])).
% 4.35/4.54  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 4.35/4.54  
% 4.35/4.54  % SZS output end Refutation
% 4.35/4.54  
% 4.35/4.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
