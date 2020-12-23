%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jEk0PwvH59

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:58 EST 2020

% Result     : Theorem 32.37s
% Output     : Refutation 32.37s
% Verified   : 
% Statistics : Number of formulae       :  187 (2358 expanded)
%              Number of leaves         :   15 ( 853 expanded)
%              Depth                    :   26
%              Number of atoms          : 1889 (21760 expanded)
%              Number of equality atoms :  180 (2351 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','28','29','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('63',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k5_xboole_0 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['55','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','74'])).

thf('79',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ X2 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','79'])).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('83',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','91'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('96',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('99',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','100','109','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('123',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('124',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k4_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('131',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X3 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X3 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['129','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['121','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('142',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('143',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('147',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['140','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','120'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('159',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X12 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['65','68','69'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['129','134','135'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['149','152','155','156','157','158','159','160','161'])).

thf('163',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['80','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('167',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','168'])).

thf('170',plain,(
    $false ),
    inference(simplify,[status(thm)],['169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jEk0PwvH59
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:41:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 32.37/32.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.37/32.56  % Solved by: fo/fo7.sh
% 32.37/32.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.37/32.56  % done 8662 iterations in 32.093s
% 32.37/32.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.37/32.56  % SZS output start Refutation
% 32.37/32.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 32.37/32.56  thf(sk_A_type, type, sk_A: $i).
% 32.37/32.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 32.37/32.56  thf(sk_B_type, type, sk_B: $i).
% 32.37/32.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 32.37/32.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 32.37/32.56  thf(t94_xboole_1, conjecture,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k2_xboole_0 @ A @ B ) =
% 32.37/32.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.37/32.56  thf(zf_stmt_0, negated_conjecture,
% 32.37/32.56    (~( ![A:$i,B:$i]:
% 32.37/32.56        ( ( k2_xboole_0 @ A @ B ) =
% 32.37/32.56          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 32.37/32.56    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 32.37/32.56  thf('0', plain,
% 32.37/32.56      (((k2_xboole_0 @ sk_A @ sk_B)
% 32.37/32.56         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 32.37/32.56             (k3_xboole_0 @ sk_A @ sk_B)))),
% 32.37/32.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.37/32.56  thf(d6_xboole_0, axiom,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k5_xboole_0 @ A @ B ) =
% 32.37/32.56       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 32.37/32.56  thf('1', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf(commutativity_k2_xboole_0, axiom,
% 32.37/32.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 32.37/32.56  thf('2', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('3', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['1', '2'])).
% 32.37/32.56  thf('4', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf('5', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['3', '4'])).
% 32.37/32.56  thf('6', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf(t48_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 32.37/32.56  thf('7', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf(t39_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 32.37/32.56  thf('8', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('9', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['7', '8'])).
% 32.37/32.56  thf('10', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('11', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('12', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['9', '10', '11'])).
% 32.37/32.56  thf(t51_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 32.37/32.56       ( A ) ))).
% 32.37/32.56  thf('13', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 32.37/32.56           = (X11))),
% 32.37/32.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.37/32.56  thf('14', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['12', '13'])).
% 32.37/32.56  thf('15', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('16', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['14', '15'])).
% 32.37/32.56  thf('17', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf('18', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('19', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('20', plain,
% 32.37/32.56      (![X0 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['18', '19'])).
% 32.37/32.56  thf('21', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 32.37/32.56           = (X11))),
% 32.37/32.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.37/32.56  thf('22', plain,
% 32.37/32.56      (![X0 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 32.37/32.56           (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['20', '21'])).
% 32.37/32.56  thf('23', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf(t52_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i,C:$i]:
% 32.37/32.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 32.37/32.56       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 32.37/32.56  thf('24', plain,
% 32.37/32.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 32.37/32.56              (k3_xboole_0 @ X13 @ X15)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t52_xboole_1])).
% 32.37/32.56  thf('25', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 32.37/32.56           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['23', '24'])).
% 32.37/32.56  thf(t41_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i,C:$i]:
% 32.37/32.56     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 32.37/32.56       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 32.37/32.56  thf('26', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('27', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('28', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 32.37/32.56           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 32.37/32.56      inference('demod', [status(thm)], ['25', '26', '27'])).
% 32.37/32.56  thf('29', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('30', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('31', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['12', '13'])).
% 32.37/32.56  thf('32', plain,
% 32.37/32.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['30', '31'])).
% 32.37/32.56  thf('33', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['22', '28', '29', '32'])).
% 32.37/32.56  thf('34', plain,
% 32.37/32.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 32.37/32.56              (k3_xboole_0 @ X13 @ X15)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t52_xboole_1])).
% 32.37/32.56  thf('35', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['33', '34'])).
% 32.37/32.56  thf('36', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('37', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['12', '13'])).
% 32.37/32.56  thf('38', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 32.37/32.56  thf('39', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('40', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ X1)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['38', '39'])).
% 32.37/32.56  thf('41', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['6', '40'])).
% 32.37/32.56  thf('42', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('43', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['41', '42'])).
% 32.37/32.56  thf('44', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['5', '43'])).
% 32.37/32.56  thf('45', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 32.37/32.56  thf('46', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['44', '45'])).
% 32.37/32.56  thf('47', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 32.37/32.56  thf('48', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('49', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['47', '48'])).
% 32.37/32.56  thf('50', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('51', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['49', '50'])).
% 32.37/32.56  thf('52', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['46', '51'])).
% 32.37/32.56  thf('53', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('54', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('55', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 32.37/32.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['53', '54'])).
% 32.37/32.56  thf('56', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('57', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('58', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 32.37/32.56      inference('sup+', [status(thm)], ['56', '57'])).
% 32.37/32.56  thf('59', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('60', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('demod', [status(thm)], ['58', '59'])).
% 32.37/32.56  thf('61', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('62', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('63', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('64', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['62', '63'])).
% 32.37/32.56  thf('65', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 32.37/32.56           = (X11))),
% 32.37/32.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.37/32.56  thf('66', plain,
% 32.37/32.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 32.37/32.56              (k3_xboole_0 @ X13 @ X15)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t52_xboole_1])).
% 32.37/32.56  thf('67', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('68', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['66', '67'])).
% 32.37/32.56  thf('69', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('70', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X12)) = (X11))),
% 32.37/32.56      inference('demod', [status(thm)], ['65', '68', '69'])).
% 32.37/32.56  thf('71', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 32.37/32.56  thf('72', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['70', '71'])).
% 32.37/32.56  thf('73', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('demod', [status(thm)], ['64', '72'])).
% 32.37/32.56  thf('74', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['61', '73'])).
% 32.37/32.56  thf('75', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['60', '74'])).
% 32.37/32.56  thf('76', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 32.37/32.56           = (k5_xboole_0 @ X2 @ X2))),
% 32.37/32.56      inference('sup+', [status(thm)], ['55', '75'])).
% 32.37/32.56  thf('77', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 32.37/32.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['53', '54'])).
% 32.37/32.56  thf('78', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['60', '74'])).
% 32.37/32.56  thf('79', plain,
% 32.37/32.56      (![X1 : $i, X2 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X1))
% 32.37/32.56           = (k5_xboole_0 @ X2 @ X2))),
% 32.37/32.56      inference('demod', [status(thm)], ['76', '77', '78'])).
% 32.37/32.56  thf('80', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X1 @ X1)
% 32.37/32.56           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['52', '79'])).
% 32.37/32.56  thf('81', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('82', plain,
% 32.37/32.56      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['16', '17'])).
% 32.37/32.56  thf('83', plain,
% 32.37/32.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 32.37/32.56              (k3_xboole_0 @ X13 @ X15)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t52_xboole_1])).
% 32.37/32.56  thf('84', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 32.37/32.56           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['82', '83'])).
% 32.37/32.56  thf('85', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('86', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k3_xboole_0 @ X0 @ X1)
% 32.37/32.56           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('demod', [status(thm)], ['84', '85'])).
% 32.37/32.56  thf('87', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['70', '71'])).
% 32.37/32.56  thf('88', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['1', '2'])).
% 32.37/32.56  thf('89', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['87', '88'])).
% 32.37/32.56  thf('90', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X12)) = (X11))),
% 32.37/32.56      inference('demod', [status(thm)], ['65', '68', '69'])).
% 32.37/32.56  thf('91', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 32.37/32.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['89', '90'])).
% 32.37/32.56  thf('92', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k3_xboole_0 @ X0 @ X1)
% 32.37/32.56           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['86', '91'])).
% 32.37/32.56  thf(t93_xboole_1, axiom,
% 32.37/32.56    (![A:$i,B:$i]:
% 32.37/32.56     ( ( k2_xboole_0 @ A @ B ) =
% 32.37/32.56       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 32.37/32.56  thf('93', plain,
% 32.37/32.56      (![X16 : $i, X17 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X16 @ X17)
% 32.37/32.56           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 32.37/32.56              (k3_xboole_0 @ X16 @ X17)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t93_xboole_1])).
% 32.37/32.56  thf('94', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X1))
% 32.37/32.56           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56              (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X1))))),
% 32.37/32.56      inference('sup+', [status(thm)], ['92', '93'])).
% 32.37/32.56  thf('95', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X12)) = (X11))),
% 32.37/32.56      inference('demod', [status(thm)], ['65', '68', '69'])).
% 32.37/32.56  thf('96', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf('97', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['95', '96'])).
% 32.37/32.56  thf('98', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('99', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('100', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 32.37/32.56           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 32.37/32.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 32.37/32.56  thf('101', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('102', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['1', '2'])).
% 32.37/32.56  thf('103', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 32.37/32.56           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['101', '102'])).
% 32.37/32.56  thf('104', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('105', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))
% 32.37/32.56           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['103', '104'])).
% 32.37/32.56  thf('106', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['61', '73'])).
% 32.37/32.56  thf('107', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 32.37/32.56           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 32.37/32.56      inference('demod', [status(thm)], ['97', '98', '99'])).
% 32.37/32.56  thf('108', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['3', '4'])).
% 32.37/32.56  thf('109', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 32.37/32.56  thf('110', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('111', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('112', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['110', '111'])).
% 32.37/32.56  thf('113', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 32.37/32.56           = (X11))),
% 32.37/32.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.37/32.56  thf('114', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['112', '113'])).
% 32.37/32.56  thf('115', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('116', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('117', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('118', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('119', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 32.37/32.56  thf('120', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['94', '100', '109', '119'])).
% 32.37/32.56  thf('121', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['81', '120'])).
% 32.37/32.56  thf('122', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ X1)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['38', '39'])).
% 32.37/32.56  thf('123', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('124', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('125', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k4_xboole_0 @ X11 @ X12))
% 32.37/32.56           = (X11))),
% 32.37/32.56      inference('cnf', [status(esa)], [t51_xboole_1])).
% 32.37/32.56  thf('126', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['124', '125'])).
% 32.37/32.56  thf('127', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ 
% 32.37/32.56           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 32.37/32.56           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ X1))),
% 32.37/32.56      inference('sup+', [status(thm)], ['123', '126'])).
% 32.37/32.56  thf('128', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('129', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['127', '128'])).
% 32.37/32.56  thf('130', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('131', plain,
% 32.37/32.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 32.37/32.56              (k3_xboole_0 @ X13 @ X15)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t52_xboole_1])).
% 32.37/32.56  thf('132', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X3))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X3)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['130', '131'])).
% 32.37/32.56  thf('133', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('134', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X3)))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X3)))),
% 32.37/32.56      inference('demod', [status(thm)], ['132', '133'])).
% 32.37/32.56  thf('135', plain,
% 32.37/32.56      (![X9 : $i, X10 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 32.37/32.56           = (k3_xboole_0 @ X9 @ X10))),
% 32.37/32.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 32.37/32.56  thf('136', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['129', '134', '135'])).
% 32.37/32.56  thf('137', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['122', '136'])).
% 32.37/32.56  thf('138', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['35', '36', '37'])).
% 32.37/32.56  thf('139', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (X0))),
% 32.37/32.56      inference('demod', [status(thm)], ['137', '138'])).
% 32.37/32.56  thf('140', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['121', '139'])).
% 32.37/32.56  thf('141', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['1', '2'])).
% 32.37/32.56  thf('142', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('143', plain,
% 32.37/32.56      (![X2 : $i, X3 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X2 @ X3)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 32.37/32.56      inference('cnf', [status(esa)], [d6_xboole_0])).
% 32.37/32.56  thf('144', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 32.37/32.56      inference('sup+', [status(thm)], ['142', '143'])).
% 32.37/32.56  thf('145', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 32.37/32.56           (k4_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))))),
% 32.37/32.56      inference('sup+', [status(thm)], ['141', '144'])).
% 32.37/32.56  thf('146', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['3', '4'])).
% 32.37/32.56  thf('147', plain,
% 32.37/32.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 32.37/32.56           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 32.37/32.56  thf('148', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 32.37/32.56           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56              (k4_xboole_0 @ X1 @ 
% 32.37/32.56               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))))),
% 32.37/32.56      inference('demod', [status(thm)], ['145', '146', '147'])).
% 32.37/32.56  thf('149', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 32.37/32.56           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))
% 32.37/32.56           = (k2_xboole_0 @ X0 @ 
% 32.37/32.56              (k4_xboole_0 @ X1 @ 
% 32.37/32.56               (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 32.37/32.56                (k4_xboole_0 @ X0 @ 
% 32.37/32.56                 (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))))))),
% 32.37/32.56      inference('sup+', [status(thm)], ['140', '148'])).
% 32.37/32.56  thf('150', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['81', '120'])).
% 32.37/32.56  thf('151', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['110', '111'])).
% 32.37/32.56  thf('152', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 32.37/32.56           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['150', '151'])).
% 32.37/32.56  thf('153', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ X0)
% 32.37/32.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['61', '73'])).
% 32.37/32.56  thf('154', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 32.37/32.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['53', '54'])).
% 32.37/32.56  thf('155', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 32.37/32.56           = (k5_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['153', '154'])).
% 32.37/32.56  thf('156', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X12)) = (X11))),
% 32.37/32.56      inference('demod', [status(thm)], ['65', '68', '69'])).
% 32.37/32.56  thf('157', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['3', '4'])).
% 32.37/32.56  thf('158', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 32.37/32.56           = (k5_xboole_0 @ X0 @ X0))),
% 32.37/32.56      inference('sup+', [status(thm)], ['153', '154'])).
% 32.37/32.56  thf('159', plain,
% 32.37/32.56      (![X11 : $i, X12 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X12)) = (X11))),
% 32.37/32.56      inference('demod', [status(thm)], ['65', '68', '69'])).
% 32.37/32.56  thf('160', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 32.37/32.56  thf('161', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.37/32.56         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))
% 32.37/32.56           = (k4_xboole_0 @ X2 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['129', '134', '135'])).
% 32.37/32.56  thf('162', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)],
% 32.37/32.56                ['149', '152', '155', '156', '157', '158', '159', '160', '161'])).
% 32.37/32.56  thf('163', plain,
% 32.37/32.56      (![X4 : $i, X5 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 32.37/32.56           = (k2_xboole_0 @ X4 @ X5))),
% 32.37/32.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 32.37/32.56  thf('164', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 32.37/32.56           = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['162', '163'])).
% 32.37/32.56  thf('165', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 32.37/32.56           (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))
% 32.37/32.56           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 32.37/32.56      inference('sup+', [status(thm)], ['80', '164'])).
% 32.37/32.56  thf('166', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k3_xboole_0 @ X0 @ X1)
% 32.37/32.56           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X0)))),
% 32.37/32.56      inference('demod', [status(thm)], ['86', '91'])).
% 32.37/32.56  thf('167', plain,
% 32.37/32.56      (![X16 : $i, X17 : $i]:
% 32.37/32.56         ((k2_xboole_0 @ X16 @ X17)
% 32.37/32.56           = (k2_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 32.37/32.56              (k3_xboole_0 @ X16 @ X17)))),
% 32.37/32.56      inference('cnf', [status(esa)], [t93_xboole_1])).
% 32.37/32.56  thf('168', plain,
% 32.37/32.56      (![X0 : $i, X1 : $i]:
% 32.37/32.56         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 32.37/32.56           = (k2_xboole_0 @ X0 @ X1))),
% 32.37/32.56      inference('demod', [status(thm)], ['165', '166', '167'])).
% 32.37/32.56  thf('169', plain,
% 32.37/32.56      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 32.37/32.56      inference('demod', [status(thm)], ['0', '168'])).
% 32.37/32.56  thf('170', plain, ($false), inference('simplify', [status(thm)], ['169'])).
% 32.37/32.56  
% 32.37/32.56  % SZS output end Refutation
% 32.37/32.56  
% 32.37/32.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
