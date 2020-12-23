%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0Lxhk31zh

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:55 EST 2020

% Result     : Theorem 12.33s
% Output     : Refutation 12.33s
% Verified   : 
% Statistics : Number of formulae       :  282 (33449 expanded)
%              Number of leaves         :   15 (11678 expanded)
%              Depth                    :   36
%              Number of atoms          : 2620 (304937 expanded)
%              Number of equality atoms :  275 (33442 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68','73','74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','85'])).

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','100'])).

thf('102',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('110',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['104','105','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('114',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['101','124'])).

thf('126',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('128',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('135',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['130','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','123'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','85'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['125','149','150','151'])).

thf('153',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('154',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('155',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['152','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('165',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','140'])).

thf('170',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['168','173'])).

thf('175',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','85'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['176','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['174','175','182','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['163','186','187'])).

thf('189',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','123'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','85'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['192','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','100'])).

thf('201',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['143','148'])).

thf('204',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206','207'])).

thf('209',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['199','208','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['125','149','150','151'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['214','217'])).

thf('219',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('220',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('221',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('222',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('224',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('226',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
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
    inference('sup+',[status(thm)],['211','212'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['227','228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['224','232'])).

thf('234',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('235',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['218','219','235'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['199','208','213'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['237','240'])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('250',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('251',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('252',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['249','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['248','253'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['243','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242','257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['236','258'])).

thf('260',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242','257'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','263'])).

thf('265',plain,(
    $false ),
    inference(simplify,[status(thm)],['264'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j0Lxhk31zh
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.33/12.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.33/12.52  % Solved by: fo/fo7.sh
% 12.33/12.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.33/12.52  % done 12770 iterations in 12.072s
% 12.33/12.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.33/12.52  % SZS output start Refutation
% 12.33/12.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.33/12.52  thf(sk_B_type, type, sk_B: $i).
% 12.33/12.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.33/12.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.33/12.52  thf(sk_A_type, type, sk_A: $i).
% 12.33/12.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.33/12.52  thf(t94_xboole_1, conjecture,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k2_xboole_0 @ A @ B ) =
% 12.33/12.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.33/12.52  thf(zf_stmt_0, negated_conjecture,
% 12.33/12.52    (~( ![A:$i,B:$i]:
% 12.33/12.52        ( ( k2_xboole_0 @ A @ B ) =
% 12.33/12.52          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 12.33/12.52    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 12.33/12.52  thf('0', plain,
% 12.33/12.52      (((k2_xboole_0 @ sk_A @ sk_B)
% 12.33/12.52         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 12.33/12.52             (k3_xboole_0 @ sk_A @ sk_B)))),
% 12.33/12.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.33/12.52  thf(d6_xboole_0, axiom,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k5_xboole_0 @ A @ B ) =
% 12.33/12.52       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 12.33/12.52  thf('1', plain,
% 12.33/12.52      (![X4 : $i, X5 : $i]:
% 12.33/12.52         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.52      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.52  thf('2', plain,
% 12.33/12.52      (![X4 : $i, X5 : $i]:
% 12.33/12.52         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.52      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.52  thf(t48_xboole_1, axiom,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.33/12.52  thf('3', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf(t39_xboole_1, axiom,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.33/12.52  thf('4', plain,
% 12.33/12.52      (![X6 : $i, X7 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.52           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.52  thf('5', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['3', '4'])).
% 12.33/12.52  thf(commutativity_k2_xboole_0, axiom,
% 12.33/12.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 12.33/12.52  thf('6', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('7', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('8', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.52      inference('demod', [status(thm)], ['5', '6', '7'])).
% 12.33/12.52  thf(t51_xboole_1, axiom,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 12.33/12.52       ( A ) ))).
% 12.33/12.52  thf('9', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('10', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.52  thf('11', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf(t40_xboole_1, axiom,
% 12.33/12.52    (![A:$i,B:$i]:
% 12.33/12.52     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.33/12.52  thf('12', plain,
% 12.33/12.52      (![X8 : $i, X9 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.52           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.52  thf('13', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.52  thf('14', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('15', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['13', '14'])).
% 12.33/12.52  thf(commutativity_k3_xboole_0, axiom,
% 12.33/12.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 12.33/12.52  thf('16', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('17', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 12.33/12.52      inference('demod', [status(thm)], ['15', '16'])).
% 12.33/12.52  thf('18', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 12.33/12.52      inference('sup+', [status(thm)], ['10', '17'])).
% 12.33/12.52  thf(t41_xboole_1, axiom,
% 12.33/12.52    (![A:$i,B:$i,C:$i]:
% 12.33/12.52     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 12.33/12.52       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 12.33/12.52  thf('19', plain,
% 12.33/12.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.52           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.52      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.52  thf('20', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('21', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.52  thf('22', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 12.33/12.52  thf('23', plain,
% 12.33/12.52      (![X4 : $i, X5 : $i]:
% 12.33/12.52         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.52      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.52  thf('24', plain,
% 12.33/12.52      (![X6 : $i, X7 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.52           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.52  thf('25', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.52  thf('26', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.52           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['24', '25'])).
% 12.33/12.52  thf('27', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.52  thf('28', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ X1)
% 12.33/12.52           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 12.33/12.52      inference('demod', [status(thm)], ['26', '27'])).
% 12.33/12.52  thf('29', plain,
% 12.33/12.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.52           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.52      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.52  thf('30', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 12.33/12.52      inference('demod', [status(thm)], ['28', '29'])).
% 12.33/12.52  thf('31', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['23', '30'])).
% 12.33/12.52  thf('32', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('33', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['31', '32'])).
% 12.33/12.52  thf('34', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.52  thf('35', plain,
% 12.33/12.52      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['33', '34'])).
% 12.33/12.52  thf('36', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.52  thf('37', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ X0)
% 12.33/12.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['35', '36'])).
% 12.33/12.52  thf('38', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['31', '32'])).
% 12.33/12.52  thf('39', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('40', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 12.33/12.52           (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['38', '39'])).
% 12.33/12.52  thf('41', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('42', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 12.33/12.52           (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['40', '41'])).
% 12.33/12.52  thf('43', plain,
% 12.33/12.52      (![X8 : $i, X9 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.52           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.52  thf('44', plain,
% 12.33/12.52      (![X6 : $i, X7 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.52           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.52  thf('45', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['43', '44'])).
% 12.33/12.52  thf('46', plain,
% 12.33/12.52      (![X6 : $i, X7 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.52           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.52  thf('47', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['45', '46'])).
% 12.33/12.52  thf('48', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['45', '46'])).
% 12.33/12.52  thf('49', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['47', '48'])).
% 12.33/12.52  thf('50', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('51', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['45', '46'])).
% 12.33/12.52  thf('52', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['49', '50', '51'])).
% 12.33/12.52  thf('53', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ 
% 12.33/12.52           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 12.33/12.52            (k3_xboole_0 @ X0 @ X0)))
% 12.33/12.52           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) @ 
% 12.33/12.52              (k3_xboole_0 @ X0 @ X0)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['42', '52'])).
% 12.33/12.52  thf('54', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('55', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 12.33/12.52           (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['40', '41'])).
% 12.33/12.52  thf('56', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('57', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ 
% 12.33/12.52           (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['40', '41'])).
% 12.33/12.52  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 12.33/12.52  thf('59', plain,
% 12.33/12.52      (![X4 : $i, X5 : $i]:
% 12.33/12.52         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.52           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.52      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.52  thf('60', plain,
% 12.33/12.52      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['58', '59'])).
% 12.33/12.52  thf('61', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.52           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['37', '60'])).
% 12.33/12.52  thf('62', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('63', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ X0) @ 
% 12.33/12.52           (k5_xboole_0 @ X0 @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['61', '62'])).
% 12.33/12.52  thf('64', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('65', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('66', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 12.33/12.52      inference('demod', [status(thm)], ['15', '16'])).
% 12.33/12.52  thf('67', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ 
% 12.33/12.52           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))
% 12.33/12.52           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 12.33/12.52              (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))))),
% 12.33/12.52      inference('sup+', [status(thm)], ['65', '66'])).
% 12.33/12.52  thf('68', plain,
% 12.33/12.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.52           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.52      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.52  thf('69', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('70', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('71', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.52  thf('72', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.52      inference('sup+', [status(thm)], ['70', '71'])).
% 12.33/12.52  thf('73', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['69', '72'])).
% 12.33/12.52  thf('74', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('75', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('76', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('77', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ X0 @ X1)
% 12.33/12.52           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 12.33/12.52      inference('demod', [status(thm)], ['67', '68', '73', '74', '75', '76'])).
% 12.33/12.52  thf('78', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('79', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['63', '64', '77', '78'])).
% 12.33/12.52  thf('80', plain,
% 12.33/12.52      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['58', '59'])).
% 12.33/12.52  thf('81', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('82', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k5_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['80', '81'])).
% 12.33/12.52  thf('83', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.52  thf('84', plain,
% 12.33/12.52      (![X0 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 12.33/12.52           = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['82', '83'])).
% 12.33/12.52  thf('85', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['79', '84'])).
% 12.33/12.52  thf('86', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['22', '85'])).
% 12.33/12.52  thf('87', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('88', plain,
% 12.33/12.52      (![X15 : $i, X16 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.52           = (X15))),
% 12.33/12.52      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.52  thf('89', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.52           = (X0))),
% 12.33/12.52      inference('sup+', [status(thm)], ['87', '88'])).
% 12.33/12.52  thf('90', plain,
% 12.33/12.52      (![X8 : $i, X9 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.52           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.52  thf('91', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.52           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['89', '90'])).
% 12.33/12.52  thf('92', plain,
% 12.33/12.52      (![X13 : $i, X14 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.52           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.52  thf('93', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ X0 @ X1)
% 12.33/12.52           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 12.33/12.52      inference('demod', [status(thm)], ['91', '92'])).
% 12.33/12.52  thf('94', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['86', '93'])).
% 12.33/12.52  thf('95', plain,
% 12.33/12.52      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.52  thf('96', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.52      inference('demod', [status(thm)], ['22', '85'])).
% 12.33/12.52  thf('97', plain,
% 12.33/12.52      (![X8 : $i, X9 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.52           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.52      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.52  thf('98', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.52      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 12.33/12.52  thf('99', plain,
% 12.33/12.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.52           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.52      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.52  thf('100', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ X1)
% 12.33/12.52           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 12.33/12.52      inference('sup+', [status(thm)], ['98', '99'])).
% 12.33/12.52  thf('101', plain,
% 12.33/12.52      (![X0 : $i, X1 : $i]:
% 12.33/12.52         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.52           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['2', '100'])).
% 12.33/12.53  thf('102', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('103', plain,
% 12.33/12.53      (![X4 : $i, X5 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.53  thf('104', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 12.33/12.53              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['102', '103'])).
% 12.33/12.53  thf('105', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('106', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.53  thf('107', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.53  thf('108', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['106', '107'])).
% 12.33/12.53  thf('109', plain,
% 12.33/12.53      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['58', '59'])).
% 12.33/12.53  thf('110', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('111', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['108', '109', '110'])).
% 12.33/12.53  thf('112', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X1)))),
% 12.33/12.53      inference('demod', [status(thm)], ['104', '105', '111'])).
% 12.33/12.53  thf('113', plain,
% 12.33/12.53      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['58', '59'])).
% 12.33/12.53  thf('114', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('115', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['113', '114'])).
% 12.33/12.53  thf('116', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('117', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['108', '109', '110'])).
% 12.33/12.53  thf('118', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['116', '117'])).
% 12.33/12.53  thf('119', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ X1)
% 12.33/12.53           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['115', '118'])).
% 12.33/12.53  thf('120', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('121', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['119', '120'])).
% 12.33/12.53  thf('122', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['69', '72'])).
% 12.33/12.53  thf('123', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['121', '122'])).
% 12.33/12.53  thf('124', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['112', '123'])).
% 12.33/12.53  thf('125', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 12.33/12.53           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['101', '124'])).
% 12.33/12.53  thf('126', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('127', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('128', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('129', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['127', '128'])).
% 12.33/12.53  thf('130', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('131', plain,
% 12.33/12.53      (![X15 : $i, X16 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.53           = (X15))),
% 12.33/12.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.53  thf('132', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.53  thf('133', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['131', '132'])).
% 12.33/12.53  thf('134', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['127', '128'])).
% 12.33/12.53  thf('135', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('136', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))))),
% 12.33/12.53      inference('demod', [status(thm)], ['133', '134', '135'])).
% 12.33/12.53  thf('137', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 12.33/12.53      inference('sup+', [status(thm)], ['130', '136'])).
% 12.33/12.53  thf('138', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['70', '71'])).
% 12.33/12.53  thf('139', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['137', '138'])).
% 12.33/12.53  thf('140', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['129', '139'])).
% 12.33/12.53  thf('141', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['126', '140'])).
% 12.33/12.53  thf('142', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['112', '123'])).
% 12.33/12.53  thf('143', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['141', '142'])).
% 12.33/12.53  thf('144', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['69', '72'])).
% 12.33/12.53  thf('145', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['22', '85'])).
% 12.33/12.53  thf('146', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['144', '145'])).
% 12.33/12.53  thf('147', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('148', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['146', '147'])).
% 12.33/12.53  thf('149', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['143', '148'])).
% 12.33/12.53  thf('150', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('151', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['137', '138'])).
% 12.33/12.53  thf('152', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['125', '149', '150', '151'])).
% 12.33/12.53  thf('153', plain,
% 12.33/12.53      (![X15 : $i, X16 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.53           = (X15))),
% 12.33/12.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.53  thf('154', plain,
% 12.33/12.53      (![X8 : $i, X9 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.53           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.53  thf('155', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('156', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 12.33/12.53           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['154', '155'])).
% 12.33/12.53  thf('157', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('158', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 12.33/12.53           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 12.33/12.53      inference('demod', [status(thm)], ['156', '157'])).
% 12.33/12.53  thf('159', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X2 @ 
% 12.33/12.53           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))
% 12.33/12.53           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['153', '158'])).
% 12.33/12.53  thf('160', plain,
% 12.33/12.53      (![X15 : $i, X16 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 12.33/12.53           = (X15))),
% 12.33/12.53      inference('cnf', [status(esa)], [t51_xboole_1])).
% 12.33/12.53  thf('161', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X2 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['159', '160'])).
% 12.33/12.53  thf('162', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X2 @ X1)
% 12.33/12.53           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['152', '161'])).
% 12.33/12.53  thf('163', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['1', '162'])).
% 12.33/12.53  thf('164', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 12.33/12.53  thf('165', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('166', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['164', '165'])).
% 12.33/12.53  thf('167', plain,
% 12.33/12.53      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['58', '59'])).
% 12.33/12.53  thf('168', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['166', '167'])).
% 12.33/12.53  thf('169', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['126', '140'])).
% 12.33/12.53  thf('170', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('171', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 12.33/12.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['169', '170'])).
% 12.33/12.53  thf('172', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('173', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 12.33/12.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 12.33/12.53      inference('demod', [status(thm)], ['171', '172'])).
% 12.33/12.53  thf('174', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 12.33/12.53              (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['168', '173'])).
% 12.33/12.53  thf('175', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('176', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('177', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['22', '85'])).
% 12.33/12.53  thf('178', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['69', '72'])).
% 12.33/12.53  thf('179', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['177', '178'])).
% 12.33/12.53  thf('180', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('181', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['179', '180'])).
% 12.33/12.53  thf('182', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['176', '181'])).
% 12.33/12.53  thf('183', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['121', '122'])).
% 12.33/12.53  thf('184', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('185', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['183', '184'])).
% 12.33/12.53  thf('186', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['174', '175', '182', '185'])).
% 12.33/12.53  thf('187', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 12.33/12.53  thf('188', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X1 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['163', '186', '187'])).
% 12.33/12.53  thf('189', plain,
% 12.33/12.53      (![X6 : $i, X7 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.53           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.53  thf('190', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['188', '189'])).
% 12.33/12.53  thf('191', plain,
% 12.33/12.53      (![X6 : $i, X7 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 12.33/12.53           = (k2_xboole_0 @ X6 @ X7))),
% 12.33/12.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 12.33/12.53  thf('192', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['190', '191'])).
% 12.33/12.53  thf('193', plain,
% 12.33/12.53      (![X8 : $i, X9 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 12.33/12.53           = (k4_xboole_0 @ X8 @ X9))),
% 12.33/12.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 12.33/12.53  thf('194', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['112', '123'])).
% 12.33/12.53  thf('195', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['193', '194'])).
% 12.33/12.53  thf('196', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('197', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['22', '85'])).
% 12.33/12.53  thf('198', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['195', '196', '197'])).
% 12.33/12.53  thf('199', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 12.33/12.53           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 12.33/12.53           = (k5_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['192', '198'])).
% 12.33/12.53  thf('200', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['2', '100'])).
% 12.33/12.53  thf('201', plain,
% 12.33/12.53      (![X4 : $i, X5 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.53  thf('202', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 12.33/12.53              (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['200', '201'])).
% 12.33/12.53  thf('203', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['143', '148'])).
% 12.33/12.53  thf('204', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('205', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['108', '109', '110'])).
% 12.33/12.53  thf('206', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('207', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['183', '184'])).
% 12.33/12.53  thf('208', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X1 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)],
% 12.33/12.53                ['202', '203', '204', '205', '206', '207'])).
% 12.33/12.53  thf('209', plain,
% 12.33/12.53      (![X4 : $i, X5 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.53  thf('210', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('211', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k5_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['209', '210'])).
% 12.33/12.53  thf('212', plain,
% 12.33/12.53      (![X4 : $i, X5 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.53  thf('213', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['211', '212'])).
% 12.33/12.53  thf('214', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k5_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['199', '208', '213'])).
% 12.33/12.53  thf('215', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['211', '212'])).
% 12.33/12.53  thf('216', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['125', '149', '150', '151'])).
% 12.33/12.53  thf('217', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['215', '216'])).
% 12.33/12.53  thf('218', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['214', '217'])).
% 12.33/12.53  thf('219', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('220', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('221', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('222', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 12.33/12.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['220', '221'])).
% 12.33/12.53  thf('223', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['8', '9'])).
% 12.33/12.53  thf('224', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 12.33/12.53           = (X2))),
% 12.33/12.53      inference('sup+', [status(thm)], ['222', '223'])).
% 12.33/12.53  thf('225', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['11', '12'])).
% 12.33/12.53  thf('226', plain,
% 12.33/12.53      (![X4 : $i, X5 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X4 @ X5)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 12.33/12.53      inference('cnf', [status(esa)], [d6_xboole_0])).
% 12.33/12.53  thf('227', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 12.33/12.53              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 12.33/12.53      inference('sup+', [status(thm)], ['225', '226'])).
% 12.33/12.53  thf('228', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['211', '212'])).
% 12.33/12.53  thf('229', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X1 @ X1)
% 12.33/12.53           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['116', '117'])).
% 12.33/12.53  thf('230', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['227', '228', '229'])).
% 12.33/12.53  thf('231', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['121', '122'])).
% 12.33/12.53  thf('232', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k4_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['230', '231'])).
% 12.33/12.53  thf('233', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['224', '232'])).
% 12.33/12.53  thf('234', plain,
% 12.33/12.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 12.33/12.53           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 12.33/12.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 12.33/12.53  thf('235', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ X0 @ X0)
% 12.33/12.53           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 12.33/12.53      inference('demod', [status(thm)], ['233', '234'])).
% 12.33/12.53  thf('236', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k5_xboole_0 @ X1 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['218', '219', '235'])).
% 12.33/12.53  thf('237', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k5_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['199', '208', '213'])).
% 12.33/12.53  thf('238', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['211', '212'])).
% 12.33/12.53  thf('239', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['190', '191'])).
% 12.33/12.53  thf('240', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['238', '239'])).
% 12.33/12.53  thf('241', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['237', '240'])).
% 12.33/12.53  thf('242', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('243', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('244', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('245', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X0 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 12.33/12.53  thf('246', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k3_xboole_0 @ X1 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['244', '245'])).
% 12.33/12.53  thf('247', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['79', '84'])).
% 12.33/12.53  thf('248', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['246', '247'])).
% 12.33/12.53  thf('249', plain,
% 12.33/12.53      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 12.33/12.53  thf('250', plain,
% 12.33/12.53      (![X13 : $i, X14 : $i]:
% 12.33/12.53         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 12.33/12.53           = (k3_xboole_0 @ X13 @ X14))),
% 12.33/12.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.33/12.53  thf('251', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 12.33/12.53           = (X2))),
% 12.33/12.53      inference('sup+', [status(thm)], ['222', '223'])).
% 12.33/12.53  thf('252', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 12.33/12.53           = (X2))),
% 12.33/12.53      inference('sup+', [status(thm)], ['250', '251'])).
% 12.33/12.53  thf('253', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 12.33/12.53           = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['249', '252'])).
% 12.33/12.53  thf('254', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['248', '253'])).
% 12.33/12.53  thf('255', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('256', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['254', '255'])).
% 12.33/12.53  thf('257', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('sup+', [status(thm)], ['243', '256'])).
% 12.33/12.53  thf('258', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['241', '242', '257'])).
% 12.33/12.53  thf('259', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ 
% 12.33/12.53           (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 12.33/12.53           (k5_xboole_0 @ X0 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 12.33/12.53      inference('sup+', [status(thm)], ['236', '258'])).
% 12.33/12.53  thf('260', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 12.33/12.53  thf('261', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (X0))),
% 12.33/12.53      inference('sup+', [status(thm)], ['183', '184'])).
% 12.33/12.53  thf('262', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 12.33/12.53           = (k2_xboole_0 @ X1 @ X0))),
% 12.33/12.53      inference('demod', [status(thm)], ['241', '242', '257'])).
% 12.33/12.53  thf('263', plain,
% 12.33/12.53      (![X0 : $i, X1 : $i]:
% 12.33/12.53         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 12.33/12.53           = (k2_xboole_0 @ X0 @ X1))),
% 12.33/12.53      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 12.33/12.53  thf('264', plain,
% 12.33/12.53      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 12.33/12.53      inference('demod', [status(thm)], ['0', '263'])).
% 12.33/12.53  thf('265', plain, ($false), inference('simplify', [status(thm)], ['264'])).
% 12.33/12.53  
% 12.33/12.53  % SZS output end Refutation
% 12.33/12.53  
% 12.33/12.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
