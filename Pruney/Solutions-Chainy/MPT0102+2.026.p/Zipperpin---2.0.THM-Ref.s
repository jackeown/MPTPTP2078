%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.drdERNdLHW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:01 EST 2020

% Result     : Theorem 14.60s
% Output     : Refutation 14.60s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 274 expanded)
%              Number of leaves         :   16 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          : 1165 (2452 expanded)
%              Number of equality atoms :  118 ( 267 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','53','54','55','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','34','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','69'])).

thf('71',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','74','83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['1','87'])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('91',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('102',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','94','97','104'])).

thf('106',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','105'])).

thf('107',plain,(
    $false ),
    inference(simplify,[status(thm)],['106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.drdERNdLHW
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.60/14.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.60/14.80  % Solved by: fo/fo7.sh
% 14.60/14.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.60/14.80  % done 4863 iterations in 14.338s
% 14.60/14.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.60/14.80  % SZS output start Refutation
% 14.60/14.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.60/14.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 14.60/14.80  thf(sk_A_type, type, sk_A: $i).
% 14.60/14.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 14.60/14.80  thf(sk_B_type, type, sk_B: $i).
% 14.60/14.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.60/14.80  thf(t95_xboole_1, conjecture,
% 14.60/14.80    (![A:$i,B:$i]:
% 14.60/14.80     ( ( k3_xboole_0 @ A @ B ) =
% 14.60/14.80       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 14.60/14.80  thf(zf_stmt_0, negated_conjecture,
% 14.60/14.80    (~( ![A:$i,B:$i]:
% 14.60/14.80        ( ( k3_xboole_0 @ A @ B ) =
% 14.60/14.80          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 14.60/14.80    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 14.60/14.80  thf('0', plain,
% 14.60/14.80      (((k3_xboole_0 @ sk_A @ sk_B)
% 14.60/14.80         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 14.60/14.80             (k2_xboole_0 @ sk_A @ sk_B)))),
% 14.60/14.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.60/14.80  thf(l98_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]:
% 14.60/14.80     ( ( k5_xboole_0 @ A @ B ) =
% 14.60/14.80       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.60/14.80  thf('1', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf(t48_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]:
% 14.60/14.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.60/14.80  thf('2', plain,
% 14.60/14.80      (![X12 : $i, X13 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 14.60/14.80           = (k3_xboole_0 @ X12 @ X13))),
% 14.60/14.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.60/14.80  thf('3', plain,
% 14.60/14.80      (![X12 : $i, X13 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 14.60/14.80           = (k3_xboole_0 @ X12 @ X13))),
% 14.60/14.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.60/14.80  thf('4', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['2', '3'])).
% 14.60/14.80  thf(t47_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]:
% 14.60/14.80     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 14.60/14.80  thf('5', plain,
% 14.60/14.80      (![X10 : $i, X11 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 14.60/14.80           = (k4_xboole_0 @ X10 @ X11))),
% 14.60/14.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 14.60/14.80  thf('6', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['4', '5'])).
% 14.60/14.80  thf(t4_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i,C:$i]:
% 14.60/14.80     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 14.60/14.80       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 14.60/14.80  thf('7', plain,
% 14.60/14.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 14.60/14.80           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 14.60/14.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.60/14.80  thf('8', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('9', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 14.60/14.80              (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['7', '8'])).
% 14.60/14.80  thf('10', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ 
% 14.60/14.80           (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))
% 14.60/14.80           = (k4_xboole_0 @ 
% 14.60/14.80              (k2_xboole_0 @ X2 @ 
% 14.60/14.80               (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))) @ 
% 14.60/14.80              (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['6', '9'])).
% 14.60/14.80  thf(t22_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 14.60/14.80  thf('11', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf(commutativity_k2_xboole_0, axiom,
% 14.60/14.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 14.60/14.80  thf('12', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.60/14.80  thf(t21_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 14.60/14.80  thf('13', plain,
% 14.60/14.80      (![X6 : $i, X7 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 14.60/14.80      inference('cnf', [status(esa)], [t21_xboole_1])).
% 14.60/14.80  thf('14', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['12', '13'])).
% 14.60/14.80  thf('15', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.60/14.80  thf('16', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('17', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['15', '16'])).
% 14.60/14.80  thf('18', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['14', '17'])).
% 14.60/14.80  thf('19', plain,
% 14.60/14.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 14.60/14.80           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 14.60/14.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.60/14.80  thf('20', plain,
% 14.60/14.80      (![X6 : $i, X7 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 14.60/14.80      inference('cnf', [status(esa)], [t21_xboole_1])).
% 14.60/14.80  thf('21', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['20', '21'])).
% 14.60/14.80  thf('23', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['18', '19', '22'])).
% 14.60/14.80  thf('24', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['4', '5'])).
% 14.60/14.80  thf('25', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('26', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['24', '25'])).
% 14.60/14.80  thf('27', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['18', '19', '22'])).
% 14.60/14.80  thf('28', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 14.60/14.80           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 14.60/14.80           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['26', '27'])).
% 14.60/14.80  thf('29', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['24', '25'])).
% 14.60/14.80  thf(commutativity_k3_xboole_0, axiom,
% 14.60/14.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 14.60/14.80  thf('30', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('31', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('32', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['30', '31'])).
% 14.60/14.80  thf('33', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['15', '16'])).
% 14.60/14.80  thf('34', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['32', '33'])).
% 14.60/14.80  thf('35', plain,
% 14.60/14.80      (![X10 : $i, X11 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 14.60/14.80           = (k4_xboole_0 @ X10 @ X11))),
% 14.60/14.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 14.60/14.80  thf('36', plain,
% 14.60/14.80      (![X12 : $i, X13 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 14.60/14.80           = (k3_xboole_0 @ X12 @ X13))),
% 14.60/14.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.60/14.80  thf('37', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['35', '36'])).
% 14.60/14.80  thf('38', plain,
% 14.60/14.80      (![X12 : $i, X13 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 14.60/14.80           = (k3_xboole_0 @ X12 @ X13))),
% 14.60/14.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.60/14.80  thf('39', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ X0)
% 14.60/14.80           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('demod', [status(thm)], ['37', '38'])).
% 14.60/14.80  thf('40', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('41', plain,
% 14.60/14.80      (![X12 : $i, X13 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 14.60/14.80           = (k3_xboole_0 @ X12 @ X13))),
% 14.60/14.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.60/14.80  thf('42', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['40', '41'])).
% 14.60/14.80  thf('43', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('44', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('demod', [status(thm)], ['42', '43'])).
% 14.60/14.80  thf('45', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 14.60/14.80           (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 14.60/14.80           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 14.60/14.80              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 14.60/14.80      inference('sup+', [status(thm)], ['39', '44'])).
% 14.60/14.80  thf('46', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('47', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('48', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('49', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 14.60/14.80      inference('sup+', [status(thm)], ['47', '48'])).
% 14.60/14.80  thf('50', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ X0)
% 14.60/14.80           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('demod', [status(thm)], ['37', '38'])).
% 14.60/14.80  thf('51', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 14.60/14.80      inference('demod', [status(thm)], ['49', '50'])).
% 14.60/14.80  thf('52', plain,
% 14.60/14.80      (![X10 : $i, X11 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 14.60/14.80           = (k4_xboole_0 @ X10 @ X11))),
% 14.60/14.80      inference('cnf', [status(esa)], [t47_xboole_1])).
% 14.60/14.80  thf('53', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['51', '52'])).
% 14.60/14.80  thf('54', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('55', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('56', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('57', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('58', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('59', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['57', '58'])).
% 14.60/14.80  thf('60', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['12', '13'])).
% 14.60/14.80  thf('61', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 14.60/14.80           = (k3_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['59', '60'])).
% 14.60/14.80  thf('62', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('63', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['61', '62'])).
% 14.60/14.80  thf('64', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['56', '63'])).
% 14.60/14.80  thf('65', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('demod', [status(thm)], ['45', '46', '53', '54', '55', '64'])).
% 14.60/14.80  thf('66', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k3_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['28', '29', '34', '65'])).
% 14.60/14.80  thf('67', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 14.60/14.80           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 14.60/14.80           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['23', '66'])).
% 14.60/14.80  thf('68', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['12', '13'])).
% 14.60/14.80  thf('69', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 14.60/14.80           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))) = (X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['67', '68'])).
% 14.60/14.80  thf('70', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ 
% 14.60/14.80           (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 14.60/14.80            (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))
% 14.60/14.80           = (k3_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['11', '69'])).
% 14.60/14.80  thf('71', plain,
% 14.60/14.80      (![X8 : $i, X9 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 14.60/14.80      inference('cnf', [status(esa)], [t22_xboole_1])).
% 14.60/14.80  thf('72', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['32', '33'])).
% 14.60/14.80  thf('73', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k4_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['51', '52'])).
% 14.60/14.80  thf('74', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k3_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 14.60/14.80  thf('75', plain,
% 14.60/14.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 14.60/14.80           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 14.60/14.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.60/14.80  thf('76', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.60/14.80  thf('77', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 14.60/14.80           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['75', '76'])).
% 14.60/14.80  thf('78', plain,
% 14.60/14.80      (![X6 : $i, X7 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 14.60/14.80      inference('cnf', [status(esa)], [t21_xboole_1])).
% 14.60/14.80  thf('79', plain,
% 14.60/14.80      (![X4 : $i, X5 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X4 @ X5)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 14.60/14.80      inference('cnf', [status(esa)], [l98_xboole_1])).
% 14.60/14.80  thf('80', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['78', '79'])).
% 14.60/14.80  thf(t6_xboole_1, axiom,
% 14.60/14.80    (![A:$i,B:$i]:
% 14.60/14.80     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 14.60/14.80  thf('81', plain,
% 14.60/14.80      (![X18 : $i, X19 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19))
% 14.60/14.80           = (k2_xboole_0 @ X18 @ X19))),
% 14.60/14.80      inference('cnf', [status(esa)], [t6_xboole_1])).
% 14.60/14.80  thf('82', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 14.60/14.80      inference('demod', [status(thm)], ['80', '81'])).
% 14.60/14.80  thf('83', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)))
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['77', '82'])).
% 14.60/14.80  thf('84', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.60/14.80  thf('85', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 14.60/14.80           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['75', '76'])).
% 14.60/14.80  thf('86', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['84', '85'])).
% 14.60/14.80  thf('87', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 14.60/14.80           = (k5_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ 
% 14.60/14.80              (k2_xboole_0 @ X1 @ 
% 14.60/14.80               (k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))))),
% 14.60/14.80      inference('demod', [status(thm)], ['10', '74', '83', '86'])).
% 14.60/14.80  thf('88', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 14.60/14.80              (k2_xboole_0 @ X0 @ 
% 14.60/14.80               (k2_xboole_0 @ X1 @ 
% 14.60/14.80                (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 14.60/14.80                 (k3_xboole_0 @ X1 @ X0))))))),
% 14.60/14.80      inference('sup+', [status(thm)], ['1', '87'])).
% 14.60/14.80  thf('89', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('90', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['57', '58'])).
% 14.60/14.80  thf('91', plain,
% 14.60/14.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 14.60/14.80           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 14.60/14.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.60/14.80  thf('92', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['12', '13'])).
% 14.60/14.80  thf('93', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 14.60/14.80           = (X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['91', '92'])).
% 14.60/14.80  thf('94', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0))
% 14.60/14.80           = (k3_xboole_0 @ X1 @ X0))),
% 14.60/14.80      inference('sup+', [status(thm)], ['90', '93'])).
% 14.60/14.80  thf('95', plain,
% 14.60/14.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.60/14.80  thf('96', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['15', '16'])).
% 14.60/14.80  thf('97', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['95', '96'])).
% 14.60/14.80  thf('98', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k5_xboole_0 @ X0 @ X1)
% 14.60/14.80           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['95', '96'])).
% 14.60/14.80  thf('99', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['24', '25'])).
% 14.60/14.80  thf('100', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))
% 14.60/14.80           = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('sup+', [status(thm)], ['98', '99'])).
% 14.60/14.80  thf('101', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.60/14.80  thf('102', plain,
% 14.60/14.80      (![X14 : $i, X15 : $i, X16 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X16)
% 14.60/14.80           = (k2_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 14.60/14.80      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.60/14.80  thf('103', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 14.60/14.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 14.60/14.80      inference('sup+', [status(thm)], ['101', '102'])).
% 14.60/14.80  thf('104', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 14.60/14.80           = (k2_xboole_0 @ X0 @ X1))),
% 14.60/14.80      inference('demod', [status(thm)], ['100', '103'])).
% 14.60/14.80  thf('105', plain,
% 14.60/14.80      (![X0 : $i, X1 : $i]:
% 14.60/14.80         ((k3_xboole_0 @ X1 @ X0)
% 14.60/14.80           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 14.60/14.80      inference('demod', [status(thm)], ['88', '89', '94', '97', '104'])).
% 14.60/14.80  thf('106', plain,
% 14.60/14.80      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 14.60/14.80      inference('demod', [status(thm)], ['0', '105'])).
% 14.60/14.80  thf('107', plain, ($false), inference('simplify', [status(thm)], ['106'])).
% 14.60/14.80  
% 14.60/14.80  % SZS output end Refutation
% 14.60/14.80  
% 14.60/14.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
