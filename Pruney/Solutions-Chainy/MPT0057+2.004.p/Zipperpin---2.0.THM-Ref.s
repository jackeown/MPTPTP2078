%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LPb6W2fKXC

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:17 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  133 (2116 expanded)
%              Number of leaves         :   15 ( 733 expanded)
%              Depth                    :   29
%              Number of atoms          : 1337 (20258 expanded)
%              Number of equality atoms :  126 (2109 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t50_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('81',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','87'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','94'])).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('100',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('108',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['98','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['98','110'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','114'])).

thf('116',plain,(
    $false ),
    inference(simplify,[status(thm)],['115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LPb6W2fKXC
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.87  % Solved by: fo/fo7.sh
% 1.65/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.87  % done 1500 iterations in 1.417s
% 1.65/1.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.87  % SZS output start Refutation
% 1.65/1.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.87  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.87  thf(t50_xboole_1, conjecture,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.65/1.87       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.65/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.87    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.87        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.65/1.87          ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 1.65/1.87    inference('cnf.neg', [status(esa)], [t50_xboole_1])).
% 1.65/1.87  thf('0', plain,
% 1.65/1.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.65/1.87         != (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 1.65/1.87             (k3_xboole_0 @ sk_A @ sk_C)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(t49_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.65/1.87       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.65/1.87  thf('1', plain,
% 1.65/1.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.87           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.87      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.87  thf('2', plain,
% 1.65/1.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.65/1.87         != (k3_xboole_0 @ sk_A @ 
% 1.65/1.87             (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_C))))),
% 1.65/1.87      inference('demod', [status(thm)], ['0', '1'])).
% 1.65/1.87  thf(t47_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.87  thf('3', plain,
% 1.65/1.87      (![X12 : $i, X13 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.87           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.87  thf('4', plain,
% 1.65/1.87      (![X12 : $i, X13 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.87           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.87  thf(t48_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.65/1.87  thf('5', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('6', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['4', '5'])).
% 1.65/1.87  thf('7', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('8', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k3_xboole_0 @ X1 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['6', '7'])).
% 1.65/1.87  thf('9', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf(commutativity_k2_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.65/1.87  thf('10', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf(t41_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.65/1.87       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.65/1.87  thf('11', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.87           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.87  thf(t39_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.65/1.87  thf('12', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('13', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['11', '12'])).
% 1.65/1.87  thf('14', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('15', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.87           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.87  thf('16', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.65/1.87           = (k4_xboole_0 @ X2 @ 
% 1.65/1.87              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 1.65/1.87      inference('sup+', [status(thm)], ['14', '15'])).
% 1.65/1.87  thf('17', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.87           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.87  thf('18', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.65/1.87           = (k4_xboole_0 @ X2 @ 
% 1.65/1.87              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.65/1.87      inference('demod', [status(thm)], ['16', '17'])).
% 1.65/1.87  thf('19', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.65/1.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.65/1.87      inference('sup+', [status(thm)], ['13', '18'])).
% 1.65/1.87  thf('20', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('21', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('22', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('23', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.87  thf('24', plain,
% 1.65/1.87      (![X12 : $i, X13 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.87           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.87  thf('25', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k4_xboole_0 @ X1 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['23', '24'])).
% 1.65/1.87  thf('26', plain,
% 1.65/1.87      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.87           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.87      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.87  thf('27', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('28', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['26', '27'])).
% 1.65/1.87  thf('29', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['25', '28'])).
% 1.65/1.87  thf('30', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('31', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1)))),
% 1.65/1.87      inference('demod', [status(thm)], ['29', '30'])).
% 1.65/1.87  thf('32', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('33', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('34', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['32', '33'])).
% 1.65/1.87  thf('35', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf('36', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf('37', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.65/1.87  thf('38', plain,
% 1.65/1.87      (![X12 : $i, X13 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.87           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.87  thf('39', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('40', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['38', '39'])).
% 1.65/1.87  thf('41', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf('42', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['40', '41'])).
% 1.65/1.87  thf('43', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['37', '42'])).
% 1.65/1.87  thf('44', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('45', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0))
% 1.65/1.87           = (k2_xboole_0 @ X0 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['43', '44'])).
% 1.65/1.87  thf('46', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.87  thf('47', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('48', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 1.65/1.87           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 1.65/1.87           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['46', '47'])).
% 1.65/1.87  thf(t23_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.65/1.87       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.65/1.87  thf('49', plain,
% 1.65/1.87      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 1.65/1.87           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X4)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.65/1.87  thf('50', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('51', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf('52', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 1.65/1.87           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.65/1.87  thf('53', plain,
% 1.65/1.87      (![X5 : $i, X6 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 1.65/1.87           = (k2_xboole_0 @ X5 @ X6))),
% 1.65/1.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.87  thf('54', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf(t40_xboole_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.87  thf('55', plain,
% 1.65/1.87      (![X7 : $i, X8 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 1.65/1.87           = (k4_xboole_0 @ X7 @ X8))),
% 1.65/1.87      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.65/1.87  thf('56', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.87           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['54', '55'])).
% 1.65/1.87  thf('57', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.87           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['53', '56'])).
% 1.65/1.87  thf('58', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.87           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('sup+', [status(thm)], ['54', '55'])).
% 1.65/1.87  thf('59', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 1.65/1.87      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.87  thf('60', plain,
% 1.65/1.87      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.87           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.87  thf('61', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 1.65/1.87      inference('demod', [status(thm)], ['59', '60'])).
% 1.65/1.87  thf('62', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('63', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.65/1.87           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('64', plain,
% 1.65/1.87      (![X14 : $i, X15 : $i]:
% 1.65/1.87         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.87           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.87  thf('65', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X1 @ X0)
% 1.65/1.87           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('66', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k3_xboole_0 @ X0 @ X0)
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['52', '65'])).
% 1.65/1.87  thf('67', plain,
% 1.65/1.87      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['45', '66'])).
% 1.65/1.87  thf('68', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ X0 @ X1)
% 1.65/1.87           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 1.65/1.87      inference('demod', [status(thm)], ['31', '67'])).
% 1.65/1.87  thf('69', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.87  thf('70', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 1.65/1.87           = (k2_xboole_0 @ X1 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['68', '69'])).
% 1.65/1.87  thf('71', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ X0)
% 1.65/1.88           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)) @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['20', '70'])).
% 1.65/1.88  thf('72', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X1)
% 1.65/1.88           = (k2_xboole_0 @ X1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['68', '69'])).
% 1.65/1.88  thf('73', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 1.65/1.88      inference('demod', [status(thm)], ['59', '60'])).
% 1.65/1.88  thf('74', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.88      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.88  thf('75', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k2_xboole_0 @ X0 @ X1)
% 1.65/1.88           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.65/1.88      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 1.65/1.88  thf('76', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.65/1.88           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['19', '75'])).
% 1.65/1.88  thf('77', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['10', '76'])).
% 1.65/1.88  thf('78', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.65/1.88           = (k4_xboole_0 @ X2 @ 
% 1.65/1.88              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.65/1.88      inference('demod', [status(thm)], ['16', '17'])).
% 1.65/1.88  thf('79', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X1 @ 
% 1.65/1.88              (k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['77', '78'])).
% 1.65/1.88  thf('80', plain,
% 1.65/1.88      (![X12 : $i, X13 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.88           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.88  thf('81', plain,
% 1.65/1.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.88           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.88  thf('82', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.65/1.88           = (k4_xboole_0 @ X2 @ 
% 1.65/1.88              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['80', '81'])).
% 1.65/1.88  thf('83', plain,
% 1.65/1.88      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 1.65/1.88           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 1.65/1.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.88  thf('84', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.65/1.88           = (k4_xboole_0 @ X2 @ 
% 1.65/1.88              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 1.65/1.88      inference('demod', [status(thm)], ['82', '83'])).
% 1.65/1.88  thf('85', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.65/1.88      inference('demod', [status(thm)], ['79', '84'])).
% 1.65/1.88  thf('86', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X0 @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X1)))),
% 1.65/1.88      inference('demod', [status(thm)], ['59', '60'])).
% 1.65/1.88  thf('87', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X1 @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['85', '86'])).
% 1.65/1.88  thf('88', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.88           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['9', '87'])).
% 1.65/1.88  thf('89', plain,
% 1.65/1.88      (![X14 : $i, X15 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.88           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.88  thf('90', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.65/1.88           = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['88', '89'])).
% 1.65/1.88  thf('91', plain,
% 1.65/1.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.88  thf('92', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.65/1.88      inference('sup+', [status(thm)], ['90', '91'])).
% 1.65/1.88  thf('93', plain,
% 1.65/1.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.88  thf('94', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.88  thf('95', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 1.65/1.88      inference('sup+', [status(thm)], ['8', '94'])).
% 1.65/1.88  thf('96', plain,
% 1.65/1.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.88  thf('97', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['6', '7'])).
% 1.65/1.88  thf('98', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['95', '96', '97'])).
% 1.65/1.88  thf('99', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.88  thf('100', plain,
% 1.65/1.88      (![X14 : $i, X15 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.88           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.88  thf('101', plain,
% 1.65/1.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.88  thf('102', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X2 @ 
% 1.65/1.88           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 1.65/1.88           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['100', '101'])).
% 1.65/1.88  thf('103', plain,
% 1.65/1.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.65/1.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.65/1.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.65/1.88  thf('104', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X2 @ 
% 1.65/1.88           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.65/1.88           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['102', '103'])).
% 1.65/1.88  thf('105', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 1.65/1.88           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.65/1.88           = (k3_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X2) @ X0))),
% 1.65/1.88      inference('sup+', [status(thm)], ['99', '104'])).
% 1.65/1.88  thf('106', plain,
% 1.65/1.88      (![X12 : $i, X13 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.65/1.88           = (k4_xboole_0 @ X12 @ X13))),
% 1.65/1.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.65/1.88  thf('107', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X2))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.88  thf('108', plain,
% 1.65/1.88      (![X14 : $i, X15 : $i]:
% 1.65/1.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.65/1.88           = (k3_xboole_0 @ X14 @ X15))),
% 1.65/1.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.65/1.88  thf('109', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.65/1.88           = (k3_xboole_0 @ X0 @ X1))),
% 1.65/1.88      inference('sup+', [status(thm)], ['88', '89'])).
% 1.65/1.88  thf('110', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.88           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.65/1.88      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 1.65/1.88  thf('111', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2)))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['98', '110'])).
% 1.65/1.88  thf('112', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.65/1.88      inference('sup+', [status(thm)], ['3', '111'])).
% 1.65/1.88  thf('113', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2)))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2)))),
% 1.65/1.88      inference('demod', [status(thm)], ['98', '110'])).
% 1.65/1.88  thf('114', plain,
% 1.65/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 1.65/1.88           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.65/1.88      inference('demod', [status(thm)], ['112', '113'])).
% 1.65/1.88  thf('115', plain,
% 1.65/1.88      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 1.65/1.88         != (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.65/1.88      inference('demod', [status(thm)], ['2', '114'])).
% 1.65/1.88  thf('116', plain, ($false), inference('simplify', [status(thm)], ['115'])).
% 1.65/1.88  
% 1.65/1.88  % SZS output end Refutation
% 1.65/1.88  
% 1.65/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
