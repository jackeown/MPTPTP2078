%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xG4RGX11CE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:56 EST 2020

% Result     : Theorem 16.44s
% Output     : Refutation 16.44s
% Verified   : 
% Statistics : Number of formulae       :  407 (238305 expanded)
%              Number of leaves         :   17 (84529 expanded)
%              Depth                    :   43
%              Number of atoms          : 4001 (2174005 expanded)
%              Number of equality atoms :  400 (238298 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

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
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['58','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ X2 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X2
      = ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88'])).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ ( k5_xboole_0 @ X1 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('117',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['115','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','35'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','99','135'])).

thf('137',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('138',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('145',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('148',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('151',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['149','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88'])).

thf('160',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['136','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('165',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['162','163','168','169'])).

thf('171',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['58','79'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('188',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['174','179'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('201',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('203',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','198','201','202','203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('212',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['175','178'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['213','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['212','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['213','218'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('226',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('233',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('234',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['231','232','233','234','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('238',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','244','245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','244','245'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['162','163','168','169'])).

thf('255',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257','258','261'])).

thf('263',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['262','268'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('271',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['269','270','271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','87','88'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['274','275'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['273','276'])).

thf('278',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('279',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('280',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['278','283'])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('287',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['284','285','286','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['273','276'])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('292',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('294',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      = X2 ) ),
    inference('sup+',[status(thm)],['292','293'])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['236','246','251','252','253','277','288','289','294'])).

thf('296',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['290','291'])).

thf('297',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('298',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['296','297'])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['206','207','210','211','223','224','295','298'])).

thf('300',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('301',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['299','300'])).

thf('302',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('303',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['301','302'])).

thf('304',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','303'])).

thf('305',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('306',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('307',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('308',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('310',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('311',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['308','309','310','311'])).

thf('313',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['305','312'])).

thf('314',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('315',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('316',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['304','316'])).

thf('318',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('319',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('320',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('321',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['318','321'])).

thf('323',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('324',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['317','322','323'])).

thf('325',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','303'])).

thf('326',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['324','325'])).

thf('327',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('328',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('329',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('330',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['328','329'])).

thf('331',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('332',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['330','331'])).

thf('333',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('334',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['58','79'])).

thf('335',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['332','335'])).

thf('337',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('338',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['336','337'])).

thf('339',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['326','327','338'])).

thf('340',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('341',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['301','302'])).

thf('342',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('343',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['341','342'])).

thf('344',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['319','320'])).

thf('345',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('346',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['343','344','345'])).

thf('347',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['340','346'])).

thf('348',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['339','347'])).

thf('349',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('350',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('351',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('352',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('353',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('354',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('355',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['353','354'])).

thf('356',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('357',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['355','356'])).

thf('358',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['352','357'])).

thf('359',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('360',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('361',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('362',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['360','361'])).

thf('363',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186'])).

thf('364',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['362','363'])).

thf('365',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('366',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('367',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['365','366'])).

thf('368',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('369',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['358','359','364','369'])).

thf('371',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['351','370'])).

thf('372',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['350','371'])).

thf('373',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['351','370'])).

thf('374',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('375',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['351','370'])).

thf('376',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['372','373','374','375'])).

thf('377',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['349','376'])).

thf('378',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['180','191'])).

thf('379',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('380',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('381',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['274','275'])).

thf('382',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('383',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('384',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 )
      = X2 ) ),
    inference('sup+',[status(thm)],['382','383'])).

thf('385',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('386',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['348','377','378','379','380','381','384','385'])).

thf('387',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','386'])).

thf('388',plain,(
    $false ),
    inference(simplify,[status(thm)],['387'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xG4RGX11CE
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.44/16.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.44/16.63  % Solved by: fo/fo7.sh
% 16.44/16.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.44/16.63  % done 10988 iterations in 16.158s
% 16.44/16.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.44/16.63  % SZS output start Refutation
% 16.44/16.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 16.44/16.63  thf(sk_B_type, type, sk_B: $i).
% 16.44/16.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 16.44/16.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.44/16.63  thf(sk_A_type, type, sk_A: $i).
% 16.44/16.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.44/16.63  thf(t94_xboole_1, conjecture,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k2_xboole_0 @ A @ B ) =
% 16.44/16.63       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 16.44/16.63  thf(zf_stmt_0, negated_conjecture,
% 16.44/16.63    (~( ![A:$i,B:$i]:
% 16.44/16.63        ( ( k2_xboole_0 @ A @ B ) =
% 16.44/16.63          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 16.44/16.63    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 16.44/16.63  thf('0', plain,
% 16.44/16.63      (((k2_xboole_0 @ sk_A @ sk_B)
% 16.44/16.63         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 16.44/16.63             (k3_xboole_0 @ sk_A @ sk_B)))),
% 16.44/16.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.44/16.63  thf(d6_xboole_0, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k5_xboole_0 @ A @ B ) =
% 16.44/16.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 16.44/16.63  thf('1', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf(commutativity_k2_xboole_0, axiom,
% 16.44/16.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 16.44/16.63  thf('2', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('3', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['1', '2'])).
% 16.44/16.63  thf('4', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('5', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('6', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf(t40_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 16.44/16.63  thf('7', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('8', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['6', '7'])).
% 16.44/16.63  thf(t41_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i,C:$i]:
% 16.44/16.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 16.44/16.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 16.44/16.63  thf('9', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf(t48_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 16.44/16.63  thf('10', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('11', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('12', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['10', '11'])).
% 16.44/16.63  thf(t47_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 16.44/16.63  thf('13', plain,
% 16.44/16.63      (![X12 : $i, X13 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 16.44/16.63           = (k4_xboole_0 @ X12 @ X13))),
% 16.44/16.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 16.44/16.63  thf('14', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf('15', plain,
% 16.44/16.63      (![X12 : $i, X13 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 16.44/16.63           = (k4_xboole_0 @ X12 @ X13))),
% 16.44/16.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 16.44/16.63  thf(t39_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 16.44/16.63  thf('16', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('17', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['15', '16'])).
% 16.44/16.63  thf('18', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('19', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['17', '18'])).
% 16.44/16.63  thf('20', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 16.44/16.63      inference('sup+', [status(thm)], ['14', '19'])).
% 16.44/16.63  thf('21', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf(t52_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i,C:$i]:
% 16.44/16.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 16.44/16.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 16.44/16.63  thf('22', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('23', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf(idempotence_k2_xboole_0, axiom,
% 16.44/16.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 16.44/16.63  thf('24', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 16.44/16.63      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 16.44/16.63  thf('25', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('26', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf('27', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['20', '21', '22', '25', '26'])).
% 16.44/16.63  thf('28', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf(t51_xboole_1, axiom,
% 16.44/16.63    (![A:$i,B:$i]:
% 16.44/16.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 16.44/16.63       ( A ) ))).
% 16.44/16.63  thf('29', plain,
% 16.44/16.63      (![X16 : $i, X17 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 16.44/16.63           = (X16))),
% 16.44/16.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 16.44/16.63  thf('30', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['28', '29'])).
% 16.44/16.63  thf('31', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('32', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('33', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('34', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('35', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['27', '34'])).
% 16.44/16.63  thf('36', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['8', '9', '35'])).
% 16.44/16.63  thf('37', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('38', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['36', '37'])).
% 16.44/16.63  thf('39', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('40', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 16.44/16.63      inference('demod', [status(thm)], ['38', '39'])).
% 16.44/16.63  thf('41', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('42', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('43', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('44', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('45', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('46', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['44', '45'])).
% 16.44/16.63  thf('47', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63           (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1)))
% 16.44/16.63           = (k3_xboole_0 @ 
% 16.44/16.63              (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)) @ 
% 16.44/16.63              (k4_xboole_0 @ X2 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['41', '46'])).
% 16.44/16.63  thf('48', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('49', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('50', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X2 @ 
% 16.44/16.63           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63            (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))))
% 16.44/16.63           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63              (k4_xboole_0 @ X2 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['47', '48', '49'])).
% 16.44/16.63  thf('51', plain,
% 16.44/16.63      (![X12 : $i, X13 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 16.44/16.63           = (k4_xboole_0 @ X12 @ X13))),
% 16.44/16.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 16.44/16.63  thf('52', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('53', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['51', '52'])).
% 16.44/16.63  thf('54', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('55', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 16.44/16.63      inference('demod', [status(thm)], ['53', '54'])).
% 16.44/16.63  thf('56', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('57', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('58', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['56', '57'])).
% 16.44/16.63  thf('59', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['27', '34'])).
% 16.44/16.63  thf('60', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('61', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['59', '60'])).
% 16.44/16.63  thf('62', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('63', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('64', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 16.44/16.63  thf('65', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('66', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['64', '65'])).
% 16.44/16.63  thf('67', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('68', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['66', '67'])).
% 16.44/16.63  thf('69', plain,
% 16.44/16.63      (![X12 : $i, X13 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 16.44/16.63           = (k4_xboole_0 @ X12 @ X13))),
% 16.44/16.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 16.44/16.63  thf('70', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('71', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['69', '70'])).
% 16.44/16.63  thf('72', plain,
% 16.44/16.63      (![X16 : $i, X17 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 16.44/16.63           = (X16))),
% 16.44/16.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 16.44/16.63  thf('73', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['71', '72'])).
% 16.44/16.63  thf('74', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf('75', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('76', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['73', '74', '75'])).
% 16.44/16.63  thf('77', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 16.44/16.63           = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['68', '76'])).
% 16.44/16.63  thf('78', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('79', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['77', '78'])).
% 16.44/16.63  thf('80', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['58', '79'])).
% 16.44/16.63  thf('81', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ 
% 16.44/16.63           (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ X2) @ 
% 16.44/16.63           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['55', '80'])).
% 16.44/16.63  thf('82', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('83', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('84', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('85', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['83', '84'])).
% 16.44/16.63  thf('86', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['27', '34'])).
% 16.44/16.63  thf('87', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((X2)
% 16.44/16.63           = (k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['85', '86'])).
% 16.44/16.63  thf('88', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('89', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['81', '82', '87', '88'])).
% 16.44/16.63  thf('90', plain,
% 16.44/16.63      (![X12 : $i, X13 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 16.44/16.63           = (k4_xboole_0 @ X12 @ X13))),
% 16.44/16.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 16.44/16.63  thf('91', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('92', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['90', '91'])).
% 16.44/16.63  thf('93', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['17', '18'])).
% 16.44/16.63  thf('94', plain,
% 16.44/16.63      (![X16 : $i, X17 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 16.44/16.63           = (X16))),
% 16.44/16.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 16.44/16.63  thf('95', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['93', '94'])).
% 16.44/16.63  thf('96', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('97', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['95', '96'])).
% 16.44/16.63  thf('98', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('99', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('100', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('101', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('102', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ (k5_xboole_0 @ X1 @ X1))
% 16.44/16.63           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['100', '101'])).
% 16.44/16.63  thf('103', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('104', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('105', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['103', '104'])).
% 16.44/16.63  thf('106', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 16.44/16.63      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 16.44/16.63  thf('107', plain,
% 16.44/16.63      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['105', '106'])).
% 16.44/16.63  thf('108', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('109', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['107', '108'])).
% 16.44/16.63  thf('110', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('111', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['109', '110'])).
% 16.44/16.63  thf('112', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf('113', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 16.44/16.63           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['111', '112'])).
% 16.44/16.63  thf('114', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['109', '110'])).
% 16.44/16.63  thf('115', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['113', '114'])).
% 16.44/16.63  thf('116', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('117', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('118', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['116', '117'])).
% 16.44/16.63  thf('119', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('120', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['118', '119'])).
% 16.44/16.63  thf('121', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['115', '120'])).
% 16.44/16.63  thf('122', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['102', '121'])).
% 16.44/16.63  thf('123', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['12', '13'])).
% 16.44/16.63  thf('124', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 16.44/16.63           = (k5_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['122', '123'])).
% 16.44/16.63  thf('125', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['8', '9', '35'])).
% 16.44/16.63  thf('126', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 16.44/16.63           (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['124', '125'])).
% 16.44/16.63  thf('127', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('128', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('129', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['126', '127', '128'])).
% 16.44/16.63  thf('130', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('131', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['129', '130'])).
% 16.44/16.63  thf('132', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['126', '127', '128'])).
% 16.44/16.63  thf('133', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['131', '132'])).
% 16.44/16.63  thf('134', plain,
% 16.44/16.63      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['105', '106'])).
% 16.44/16.63  thf('135', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('136', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['92', '99', '135'])).
% 16.44/16.63  thf('137', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('138', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('139', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('140', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63           (k4_xboole_0 @ X2 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['138', '139'])).
% 16.44/16.63  thf('141', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('142', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X2 @ 
% 16.44/16.63           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1)))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['140', '141'])).
% 16.44/16.63  thf('143', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['137', '142'])).
% 16.44/16.63  thf('144', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('145', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('146', plain,
% 16.44/16.63      (![X0 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['144', '145'])).
% 16.44/16.63  thf('147', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('148', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['146', '147'])).
% 16.44/16.63  thf('149', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['143', '148'])).
% 16.44/16.63  thf('150', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('151', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('152', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['150', '151'])).
% 16.44/16.63  thf('153', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('154', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 16.44/16.63  thf('155', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('156', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 16.44/16.63  thf('157', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['149', '156'])).
% 16.44/16.63  thf('158', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 16.44/16.63  thf('159', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['81', '82', '87', '88'])).
% 16.44/16.63  thf('160', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['146', '147'])).
% 16.44/16.63  thf('161', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 16.44/16.63  thf('162', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['136', '161'])).
% 16.44/16.63  thf('163', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['81', '82', '87', '88'])).
% 16.44/16.63  thf('164', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('165', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('166', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['164', '165'])).
% 16.44/16.63  thf('167', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('168', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['166', '167'])).
% 16.44/16.63  thf('169', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('170', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['162', '163', '168', '169'])).
% 16.44/16.63  thf('171', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('172', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['170', '171'])).
% 16.44/16.63  thf('173', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('174', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['172', '173'])).
% 16.44/16.63  thf('175', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('176', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['58', '79'])).
% 16.44/16.63  thf('177', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['44', '45'])).
% 16.44/16.63  thf('178', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['176', '177'])).
% 16.44/16.63  thf('179', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['175', '178'])).
% 16.44/16.63  thf('180', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['174', '179'])).
% 16.44/16.63  thf('181', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['73', '74', '75'])).
% 16.44/16.63  thf('182', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['77', '78'])).
% 16.44/16.63  thf('183', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['181', '182'])).
% 16.44/16.63  thf('184', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('185', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('186', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['93', '94'])).
% 16.44/16.63  thf('187', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 16.44/16.63  thf('188', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('189', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['187', '188'])).
% 16.44/16.63  thf('190', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('191', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['189', '190'])).
% 16.44/16.63  thf('192', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('193', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['174', '179'])).
% 16.44/16.63  thf('194', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['192', '193'])).
% 16.44/16.63  thf('195', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['89', '194'])).
% 16.44/16.63  thf('196', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['81', '82', '87', '88'])).
% 16.44/16.63  thf('197', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['192', '193'])).
% 16.44/16.63  thf('198', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['195', '196', '197'])).
% 16.44/16.63  thf('199', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['195', '196', '197'])).
% 16.44/16.63  thf('200', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('201', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['199', '200'])).
% 16.44/16.63  thf('202', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['146', '147'])).
% 16.44/16.63  thf('203', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('204', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['27', '34'])).
% 16.44/16.63  thf('205', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X2 @ 
% 16.44/16.63           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63            (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))))
% 16.44/16.63           = (k4_xboole_0 @ X2 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)],
% 16.44/16.63                ['50', '198', '201', '202', '203', '204'])).
% 16.44/16.63  thf('206', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ 
% 16.44/16.63           (k2_xboole_0 @ X0 @ 
% 16.44/16.63            (k4_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ 
% 16.44/16.63             (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))))
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['40', '205'])).
% 16.44/16.63  thf('207', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('208', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('209', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 16.44/16.63  thf('210', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['208', '209'])).
% 16.44/16.63  thf('211', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('212', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('213', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('214', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['175', '178'])).
% 16.44/16.63  thf('215', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['93', '94'])).
% 16.44/16.63  thf('216', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['214', '215'])).
% 16.44/16.63  thf('217', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('218', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['216', '217'])).
% 16.44/16.63  thf('219', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['213', '218'])).
% 16.44/16.63  thf('220', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['212', '219'])).
% 16.44/16.63  thf('221', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['213', '218'])).
% 16.44/16.63  thf('222', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('223', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 16.44/16.63  thf('224', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('225', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('226', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('227', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('sup+', [status(thm)], ['225', '226'])).
% 16.44/16.63  thf('228', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('229', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('demod', [status(thm)], ['227', '228'])).
% 16.44/16.63  thf('230', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('demod', [status(thm)], ['227', '228'])).
% 16.44/16.63  thf('231', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 16.44/16.63           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 16.44/16.63            (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))
% 16.44/16.63           = (k2_xboole_0 @ 
% 16.44/16.63              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63               (k4_xboole_0 @ X0 @ X1)) @ 
% 16.44/16.63              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 16.44/16.63               (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))))),
% 16.44/16.63      inference('sup+', [status(thm)], ['229', '230'])).
% 16.44/16.63  thf('232', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('demod', [status(thm)], ['227', '228'])).
% 16.44/16.63  thf('233', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('234', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('235', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('236', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 16.44/16.63           (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k2_xboole_0 @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ 
% 16.44/16.63               (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))) @ 
% 16.44/16.63              (k4_xboole_0 @ X1 @ 
% 16.44/16.63               (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))))),
% 16.44/16.63      inference('demod', [status(thm)], ['231', '232', '233', '234', '235'])).
% 16.44/16.63  thf('237', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('238', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('239', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 16.44/16.63              (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['237', '238'])).
% 16.44/16.63  thf('240', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('241', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('demod', [status(thm)], ['239', '240'])).
% 16.44/16.63  thf('242', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('243', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 16.44/16.63  thf('244', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['242', '243'])).
% 16.44/16.63  thf('245', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('246', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['241', '244', '245'])).
% 16.44/16.63  thf('247', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['1', '2'])).
% 16.44/16.63  thf('248', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 16.44/16.63  thf('249', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['247', '248'])).
% 16.44/16.63  thf('250', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('251', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 16.44/16.63      inference('demod', [status(thm)], ['249', '250'])).
% 16.44/16.63  thf('252', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['241', '244', '245'])).
% 16.44/16.63  thf('253', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 16.44/16.63  thf('254', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['162', '163', '168', '169'])).
% 16.44/16.63  thf('255', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('256', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)
% 16.44/16.63           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))))),
% 16.44/16.63      inference('sup+', [status(thm)], ['254', '255'])).
% 16.44/16.63  thf('257', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('258', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 16.44/16.63  thf('259', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('260', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('261', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['259', '260'])).
% 16.44/16.63  thf('262', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['256', '257', '258', '261'])).
% 16.44/16.63  thf('263', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('264', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['42', '43'])).
% 16.44/16.63  thf('265', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['263', '264'])).
% 16.44/16.63  thf('266', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('267', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['27', '34'])).
% 16.44/16.63  thf('268', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['265', '266', '267'])).
% 16.44/16.63  thf('269', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['262', '268'])).
% 16.44/16.63  thf('270', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 16.44/16.63  thf('271', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('272', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 16.44/16.63  thf('273', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['269', '270', '271', '272'])).
% 16.44/16.63  thf('274', plain,
% 16.44/16.63      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['23', '24'])).
% 16.44/16.63  thf('275', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['81', '82', '87', '88'])).
% 16.44/16.63  thf('276', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['274', '275'])).
% 16.44/16.63  thf('277', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['273', '276'])).
% 16.44/16.63  thf('278', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('279', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('280', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('281', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['279', '280'])).
% 16.44/16.63  thf('282', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('283', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['281', '282'])).
% 16.44/16.63  thf('284', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['278', '283'])).
% 16.44/16.63  thf('285', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('286', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('287', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('288', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['284', '285', '286', '287'])).
% 16.44/16.63  thf('289', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['273', '276'])).
% 16.44/16.63  thf('290', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['118', '119'])).
% 16.44/16.63  thf('291', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['126', '127', '128'])).
% 16.44/16.63  thf('292', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 16.44/16.63           = (X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['290', '291'])).
% 16.44/16.63  thf('293', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['259', '260'])).
% 16.44/16.63  thf('294', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 16.44/16.63           = (X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['292', '293'])).
% 16.44/16.63  thf('295', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)],
% 16.44/16.63                ['236', '246', '251', '252', '253', '277', '288', '289', '294'])).
% 16.44/16.63  thf('296', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 16.44/16.63           = (X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['290', '291'])).
% 16.44/16.63  thf('297', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('298', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 16.44/16.63           = (X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['296', '297'])).
% 16.44/16.63  thf('299', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)],
% 16.44/16.63                ['206', '207', '210', '211', '223', '224', '295', '298'])).
% 16.44/16.63  thf('300', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('301', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['299', '300'])).
% 16.44/16.63  thf('302', plain,
% 16.44/16.63      (![X5 : $i, X6 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 16.44/16.63           = (k2_xboole_0 @ X5 @ X6))),
% 16.44/16.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 16.44/16.63  thf('303', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['301', '302'])).
% 16.44/16.63  thf('304', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['5', '303'])).
% 16.44/16.63  thf('305', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['220', '221', '222'])).
% 16.44/16.63  thf('306', plain,
% 16.44/16.63      (![X7 : $i, X8 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 16.44/16.63           = (k4_xboole_0 @ X7 @ X8))),
% 16.44/16.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 16.44/16.63  thf('307', plain,
% 16.44/16.63      (![X2 : $i, X3 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X2 @ X3)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 16.44/16.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 16.44/16.63  thf('308', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 16.44/16.63      inference('sup+', [status(thm)], ['306', '307'])).
% 16.44/16.63  thf('309', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('310', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)], ['61', '62', '63'])).
% 16.44/16.63  thf('311', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['133', '134'])).
% 16.44/16.63  thf('312', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['308', '309', '310', '311'])).
% 16.44/16.63  thf('313', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['305', '312'])).
% 16.44/16.63  thf('314', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('315', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['77', '78'])).
% 16.44/16.63  thf('316', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['313', '314', '315'])).
% 16.44/16.63  thf('317', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['304', '316'])).
% 16.44/16.63  thf('318', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('319', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['143', '148'])).
% 16.44/16.63  thf('320', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('321', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['319', '320'])).
% 16.44/16.63  thf('322', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['318', '321'])).
% 16.44/16.63  thf('323', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('324', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['317', '322', '323'])).
% 16.44/16.63  thf('325', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['5', '303'])).
% 16.44/16.63  thf('326', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['324', '325'])).
% 16.44/16.63  thf('327', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('328', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('329', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('330', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['328', '329'])).
% 16.44/16.63  thf('331', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 16.44/16.63           = (k5_xboole_0 @ X0 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['122', '123'])).
% 16.44/16.63  thf('332', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['330', '331'])).
% 16.44/16.63  thf('333', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.44/16.63  thf('334', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['58', '79'])).
% 16.44/16.63  thf('335', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['333', '334'])).
% 16.44/16.63  thf('336', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ 
% 16.44/16.63           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1)) @ 
% 16.44/16.63           (k5_xboole_0 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['332', '335'])).
% 16.44/16.63  thf('337', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 16.44/16.63  thf('338', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['336', '337'])).
% 16.44/16.63  thf('339', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['326', '327', '338'])).
% 16.44/16.63  thf('340', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('341', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k2_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['301', '302'])).
% 16.44/16.63  thf('342', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['313', '314', '315'])).
% 16.44/16.63  thf('343', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 16.44/16.63           = (k5_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['341', '342'])).
% 16.44/16.63  thf('344', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['319', '320'])).
% 16.44/16.63  thf('345', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('346', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k5_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['343', '344', '345'])).
% 16.44/16.63  thf('347', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['340', '346'])).
% 16.44/16.63  thf('348', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ 
% 16.44/16.63           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)) @ 
% 16.44/16.63           (k2_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['339', '347'])).
% 16.44/16.63  thf('349', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('350', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['192', '193'])).
% 16.44/16.63  thf('351', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('352', plain,
% 16.44/16.63      (![X14 : $i, X15 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 16.44/16.63           = (k3_xboole_0 @ X14 @ X15))),
% 16.44/16.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 16.44/16.63  thf('353', plain,
% 16.44/16.63      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 16.44/16.63           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 16.44/16.63  thf('354', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 16.44/16.63  thf('355', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 16.44/16.63           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['353', '354'])).
% 16.44/16.63  thf('356', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['195', '196', '197'])).
% 16.44/16.63  thf('357', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 16.44/16.63           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['355', '356'])).
% 16.44/16.63  thf('358', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 16.44/16.63           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['352', '357'])).
% 16.44/16.63  thf('359', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['83', '84'])).
% 16.44/16.63  thf('360', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['172', '173'])).
% 16.44/16.63  thf('361', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['313', '314', '315'])).
% 16.44/16.63  thf('362', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['360', '361'])).
% 16.44/16.63  thf('363', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['183', '184', '185', '186'])).
% 16.44/16.63  thf('364', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k3_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['362', '363'])).
% 16.44/16.63  thf('365', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['97', '98'])).
% 16.44/16.63  thf('366', plain,
% 16.44/16.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 16.44/16.63           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 16.44/16.63              (k3_xboole_0 @ X18 @ X20)))),
% 16.44/16.63      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.44/16.63  thf('367', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 16.44/16.63              (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['365', '366'])).
% 16.44/16.63  thf('368', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['259', '260'])).
% 16.44/16.63  thf('369', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X0 @ X1))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 16.44/16.63      inference('demod', [status(thm)], ['367', '368'])).
% 16.44/16.63  thf('370', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0))),
% 16.44/16.63      inference('demod', [status(thm)], ['358', '359', '364', '369'])).
% 16.44/16.63  thf('371', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['351', '370'])).
% 16.44/16.63  thf('372', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['350', '371'])).
% 16.44/16.63  thf('373', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['351', '370'])).
% 16.44/16.63  thf('374', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X0 @ X1)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['192', '193'])).
% 16.44/16.63  thf('375', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))
% 16.44/16.63           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['351', '370'])).
% 16.44/16.63  thf('376', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 16.44/16.63      inference('demod', [status(thm)], ['372', '373', '374', '375'])).
% 16.44/16.63  thf('377', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['349', '376'])).
% 16.44/16.63  thf('378', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.44/16.63      inference('sup+', [status(thm)], ['180', '191'])).
% 16.44/16.63  thf('379', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['208', '209'])).
% 16.44/16.63  thf('380', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 16.44/16.63      inference('sup+', [status(thm)], ['199', '200'])).
% 16.44/16.63  thf('381', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 16.44/16.63           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['274', '275'])).
% 16.44/16.63  thf('382', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ X0 @ X0)
% 16.44/16.63           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 16.44/16.63      inference('demod', [status(thm)], ['118', '119'])).
% 16.44/16.63  thf('383', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['129', '130'])).
% 16.44/16.63  thf('384', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.44/16.63         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2)
% 16.44/16.63           = (X2))),
% 16.44/16.63      inference('sup+', [status(thm)], ['382', '383'])).
% 16.44/16.63  thf('385', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 16.44/16.63      inference('sup+', [status(thm)], ['3', '4'])).
% 16.44/16.63  thf('386', plain,
% 16.44/16.63      (![X0 : $i, X1 : $i]:
% 16.44/16.63         ((k2_xboole_0 @ X1 @ X0)
% 16.44/16.63           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 16.44/16.63      inference('demod', [status(thm)],
% 16.44/16.63                ['348', '377', '378', '379', '380', '381', '384', '385'])).
% 16.44/16.63  thf('387', plain,
% 16.44/16.63      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 16.44/16.63      inference('demod', [status(thm)], ['0', '386'])).
% 16.44/16.63  thf('388', plain, ($false), inference('simplify', [status(thm)], ['387'])).
% 16.44/16.63  
% 16.44/16.63  % SZS output end Refutation
% 16.44/16.63  
% 16.44/16.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
