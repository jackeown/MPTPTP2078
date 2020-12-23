%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnoMkD2bOQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:19 EST 2020

% Result     : Theorem 15.73s
% Output     : Refutation 15.73s
% Verified   : 
% Statistics : Number of formulae       :  152 (10686 expanded)
%              Number of leaves         :   18 (3849 expanded)
%              Depth                    :   27
%              Number of atoms          : 1340 (95798 expanded)
%              Number of equality atoms :  145 (10679 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

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
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','21','22','23','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['63','79'])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','62'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('108',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('127',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','124','125','126','127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','129'])).

thf('131',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','130'])).

thf('132',plain,(
    $false ),
    inference(simplify,[status(thm)],['131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnoMkD2bOQ
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 15.73/15.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 15.73/15.93  % Solved by: fo/fo7.sh
% 15.73/15.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 15.73/15.93  % done 8827 iterations in 15.476s
% 15.73/15.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 15.73/15.93  % SZS output start Refutation
% 15.73/15.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 15.73/15.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 15.73/15.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 15.73/15.93  thf(sk_B_type, type, sk_B: $i).
% 15.73/15.93  thf(sk_A_type, type, sk_A: $i).
% 15.73/15.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 15.73/15.93  thf(t101_xboole_1, conjecture,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k5_xboole_0 @ A @ B ) =
% 15.73/15.93       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.73/15.93  thf(zf_stmt_0, negated_conjecture,
% 15.73/15.93    (~( ![A:$i,B:$i]:
% 15.73/15.93        ( ( k5_xboole_0 @ A @ B ) =
% 15.73/15.93          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 15.73/15.93    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 15.73/15.93  thf('0', plain,
% 15.73/15.93      (((k5_xboole_0 @ sk_A @ sk_B)
% 15.73/15.93         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 15.73/15.93             (k3_xboole_0 @ sk_A @ sk_B)))),
% 15.73/15.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 15.73/15.93  thf(t93_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k2_xboole_0 @ A @ B ) =
% 15.73/15.93       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.73/15.93  thf('1', plain,
% 15.73/15.93      (![X20 : $i, X21 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X20 @ X21)
% 15.73/15.93           = (k2_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 15.73/15.93              (k3_xboole_0 @ X20 @ X21)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t93_xboole_1])).
% 15.73/15.93  thf(commutativity_k2_xboole_0, axiom,
% 15.73/15.93    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 15.73/15.93  thf('2', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('3', plain,
% 15.73/15.93      (![X20 : $i, X21 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X20 @ X21)
% 15.73/15.93           = (k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 15.73/15.93              (k5_xboole_0 @ X20 @ X21)))),
% 15.73/15.93      inference('demod', [status(thm)], ['1', '2'])).
% 15.73/15.93  thf(t48_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 15.73/15.93  thf('4', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf('5', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf('6', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['4', '5'])).
% 15.73/15.93  thf(commutativity_k3_xboole_0, axiom,
% 15.73/15.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 15.73/15.93  thf('7', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf(t47_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 15.73/15.93  thf('8', plain,
% 15.73/15.93      (![X11 : $i, X12 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 15.73/15.93           = (k4_xboole_0 @ X11 @ X12))),
% 15.73/15.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.73/15.93  thf('9', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['7', '8'])).
% 15.73/15.93  thf('10', plain,
% 15.73/15.93      (![X0 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['6', '9'])).
% 15.73/15.93  thf('11', plain,
% 15.73/15.93      (![X11 : $i, X12 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 15.73/15.93           = (k4_xboole_0 @ X11 @ X12))),
% 15.73/15.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.73/15.93  thf(t39_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 15.73/15.93  thf('12', plain,
% 15.73/15.93      (![X6 : $i, X7 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 15.73/15.93           = (k2_xboole_0 @ X6 @ X7))),
% 15.73/15.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.73/15.93  thf('13', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['11', '12'])).
% 15.73/15.93  thf('14', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('15', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['13', '14'])).
% 15.73/15.93  thf('16', plain,
% 15.73/15.93      (![X0 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 15.73/15.93           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))
% 15.73/15.93           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))))),
% 15.73/15.93      inference('sup+', [status(thm)], ['10', '15'])).
% 15.73/15.93  thf('17', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf('18', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('19', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf(t51_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 15.73/15.93       ( A ) ))).
% 15.73/15.93  thf('20', plain,
% 15.73/15.93      (![X15 : $i, X16 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.73/15.93           = (X15))),
% 15.73/15.93      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.73/15.93  thf('21', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 15.73/15.93           = (X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['19', '20'])).
% 15.73/15.93  thf('22', plain,
% 15.73/15.93      (![X0 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['6', '9'])).
% 15.73/15.93  thf('23', plain,
% 15.73/15.93      (![X6 : $i, X7 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 15.73/15.93           = (k2_xboole_0 @ X6 @ X7))),
% 15.73/15.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.73/15.93  thf('24', plain,
% 15.73/15.93      (![X0 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['6', '9'])).
% 15.73/15.93  thf(t100_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 15.73/15.93  thf('25', plain,
% 15.73/15.93      (![X4 : $i, X5 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X4 @ X5)
% 15.73/15.93           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.73/15.93  thf('26', plain,
% 15.73/15.93      (![X0 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['24', '25'])).
% 15.73/15.93  thf('27', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf(t98_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i]:
% 15.73/15.93     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 15.73/15.93  thf('28', plain,
% 15.73/15.93      (![X22 : $i, X23 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X22 @ X23)
% 15.73/15.93           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 15.73/15.93  thf('29', plain,
% 15.73/15.93      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['26', '27', '28'])).
% 15.73/15.93  thf('30', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)],
% 15.73/15.93                ['16', '17', '18', '21', '22', '23', '29'])).
% 15.73/15.93  thf('31', plain,
% 15.73/15.93      (![X4 : $i, X5 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X4 @ X5)
% 15.73/15.93           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.73/15.93  thf('32', plain,
% 15.73/15.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['30', '31'])).
% 15.73/15.93  thf(t41_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i,C:$i]:
% 15.73/15.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 15.73/15.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 15.73/15.93  thf('33', plain,
% 15.73/15.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 15.73/15.93           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 15.73/15.93  thf('34', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['32', '33'])).
% 15.73/15.93  thf('35', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['32', '33'])).
% 15.73/15.93  thf('36', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['4', '5'])).
% 15.73/15.93  thf('37', plain,
% 15.73/15.93      (![X11 : $i, X12 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 15.73/15.93           = (k4_xboole_0 @ X11 @ X12))),
% 15.73/15.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.73/15.93  thf('38', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['36', '37'])).
% 15.73/15.93  thf('39', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['13', '14'])).
% 15.73/15.93  thf('40', plain,
% 15.73/15.93      (![X15 : $i, X16 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 15.73/15.93           = (X15))),
% 15.73/15.93      inference('cnf', [status(esa)], [t51_xboole_1])).
% 15.73/15.93  thf('41', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['39', '40'])).
% 15.73/15.93  thf('42', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['38', '41'])).
% 15.73/15.93  thf('43', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0))
% 15.73/15.93           = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['35', '42'])).
% 15.73/15.93  thf('44', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['32', '33'])).
% 15.73/15.93  thf('45', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 15.73/15.93           (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))
% 15.73/15.93           = (k4_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['43', '44'])).
% 15.73/15.93  thf('46', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf('47', plain,
% 15.73/15.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['30', '31'])).
% 15.73/15.93  thf('48', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 15.73/15.93  thf('49', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['36', '37'])).
% 15.73/15.93  thf('50', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X0 @ X0)
% 15.73/15.93           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['48', '49'])).
% 15.73/15.93  thf('51', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X0 @ X0)
% 15.73/15.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('demod', [status(thm)], ['34', '50'])).
% 15.73/15.93  thf('52', plain,
% 15.73/15.93      (![X13 : $i, X14 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 15.73/15.93           = (k3_xboole_0 @ X13 @ X14))),
% 15.73/15.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 15.73/15.93  thf('53', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 15.73/15.93           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['51', '52'])).
% 15.73/15.93  thf('54', plain,
% 15.73/15.93      (![X6 : $i, X7 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 15.73/15.93           = (k2_xboole_0 @ X6 @ X7))),
% 15.73/15.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.73/15.93  thf('55', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 15.73/15.93  thf('56', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 15.73/15.93           = (X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['19', '20'])).
% 15.73/15.93  thf('57', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 15.73/15.93           (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['55', '56'])).
% 15.73/15.93  thf('58', plain,
% 15.73/15.93      (![X6 : $i, X7 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 15.73/15.93           = (k2_xboole_0 @ X6 @ X7))),
% 15.73/15.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 15.73/15.93  thf('59', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 15.73/15.93      inference('demod', [status(thm)], ['57', '58'])).
% 15.73/15.93  thf('60', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0)
% 15.73/15.93           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['54', '59'])).
% 15.73/15.93  thf('61', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 15.73/15.93      inference('demod', [status(thm)], ['57', '58'])).
% 15.73/15.93  thf('62', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 15.73/15.93      inference('demod', [status(thm)], ['60', '61'])).
% 15.73/15.93  thf('63', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('demod', [status(thm)], ['53', '62'])).
% 15.73/15.93  thf('64', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf('65', plain,
% 15.73/15.93      (![X11 : $i, X12 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 15.73/15.93           = (k4_xboole_0 @ X11 @ X12))),
% 15.73/15.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 15.73/15.93  thf('66', plain,
% 15.73/15.93      (![X22 : $i, X23 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X22 @ X23)
% 15.73/15.93           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 15.73/15.93  thf('67', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['65', '66'])).
% 15.73/15.93  thf('68', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('69', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['67', '68'])).
% 15.73/15.93  thf('70', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['39', '40'])).
% 15.73/15.93  thf('71', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X1)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['69', '70'])).
% 15.73/15.93  thf('72', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['64', '71'])).
% 15.73/15.93  thf('73', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1)))),
% 15.73/15.93      inference('demod', [status(thm)], ['60', '61'])).
% 15.73/15.93  thf('74', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['64', '71'])).
% 15.73/15.93  thf('75', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X1) @ X0) @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['73', '74'])).
% 15.73/15.93  thf('76', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 15.73/15.93  thf(t91_xboole_1, axiom,
% 15.73/15.93    (![A:$i,B:$i,C:$i]:
% 15.73/15.93     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 15.73/15.93       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 15.73/15.93  thf('77', plain,
% 15.73/15.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 15.73/15.93           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 15.73/15.93  thf('78', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('79', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['72', '78'])).
% 15.73/15.93  thf('80', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['63', '79'])).
% 15.73/15.93  thf('81', plain,
% 15.73/15.93      (![X22 : $i, X23 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X22 @ X23)
% 15.73/15.93           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t98_xboole_1])).
% 15.73/15.93  thf('82', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('83', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['81', '82'])).
% 15.73/15.93  thf('84', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 15.73/15.93           = (k4_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['80', '83'])).
% 15.73/15.93  thf('85', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['3', '84'])).
% 15.73/15.93  thf('86', plain,
% 15.73/15.93      (![X20 : $i, X21 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X20 @ X21)
% 15.73/15.93           = (k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 15.73/15.93              (k5_xboole_0 @ X20 @ X21)))),
% 15.73/15.93      inference('demod', [status(thm)], ['1', '2'])).
% 15.73/15.93  thf('87', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('88', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 15.73/15.93      inference('demod', [status(thm)], ['53', '62'])).
% 15.73/15.93  thf('89', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['87', '88'])).
% 15.73/15.93  thf('90', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X1 @ X0)
% 15.73/15.93           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['86', '89'])).
% 15.73/15.93  thf('91', plain,
% 15.73/15.93      (![X20 : $i, X21 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X20 @ X21)
% 15.73/15.93           = (k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ 
% 15.73/15.93              (k5_xboole_0 @ X20 @ X21)))),
% 15.73/15.93      inference('demod', [status(thm)], ['1', '2'])).
% 15.73/15.93  thf('92', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 15.73/15.93  thf('93', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['81', '82'])).
% 15.73/15.93  thf('94', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X1 @ X0)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['92', '93'])).
% 15.73/15.93  thf('95', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['91', '94'])).
% 15.73/15.93  thf('96', plain,
% 15.73/15.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 15.73/15.93           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 15.73/15.93  thf('97', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X1 @ X0)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['92', '93'])).
% 15.73/15.93  thf('98', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['95', '96', '97'])).
% 15.73/15.93  thf('99', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf('100', plain,
% 15.73/15.93      (![X4 : $i, X5 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X4 @ X5)
% 15.73/15.93           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 15.73/15.93  thf('101', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['99', '100'])).
% 15.73/15.93  thf('102', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('103', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['101', '102'])).
% 15.73/15.93  thf('104', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k3_xboole_0 @ X0 @ X1))),
% 15.73/15.93      inference('demod', [status(thm)], ['98', '103'])).
% 15.73/15.93  thf('105', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 15.73/15.93           (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))
% 15.73/15.93           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['90', '104'])).
% 15.73/15.93  thf('106', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 15.73/15.93      inference('demod', [status(thm)], ['57', '58'])).
% 15.73/15.93  thf('107', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 15.73/15.93  thf('108', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf('109', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['39', '40'])).
% 15.73/15.93  thf('110', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['108', '109'])).
% 15.73/15.93  thf('111', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['107', '110'])).
% 15.73/15.93  thf('112', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['106', '111'])).
% 15.73/15.93  thf('113', plain,
% 15.73/15.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 15.73/15.93           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 15.73/15.93  thf('114', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X0 @ X0)
% 15.73/15.93           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1))))),
% 15.73/15.93      inference('sup+', [status(thm)], ['112', '113'])).
% 15.73/15.93  thf('115', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('116', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1))
% 15.73/15.93           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X0 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['114', '115'])).
% 15.73/15.93  thf('117', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X1 @ X1))),
% 15.73/15.93      inference('sup+', [status(thm)], ['106', '111'])).
% 15.73/15.93  thf('118', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('119', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X1) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['117', '118'])).
% 15.73/15.93  thf('120', plain,
% 15.73/15.93      (![X1 : $i, X2 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ X1)) = (X2))),
% 15.73/15.93      inference('demod', [status(thm)], ['116', '119'])).
% 15.73/15.93  thf('121', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 15.73/15.93  thf('122', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('sup+', [status(thm)], ['120', '121'])).
% 15.73/15.93  thf('123', plain,
% 15.73/15.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 15.73/15.93           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 15.73/15.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 15.73/15.93  thf('124', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 15.73/15.93           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['122', '123'])).
% 15.73/15.93  thf('125', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['81', '82'])).
% 15.73/15.93  thf('126', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k3_xboole_0 @ X0 @ X1)
% 15.73/15.93           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['101', '102'])).
% 15.73/15.93  thf('127', plain,
% 15.73/15.93      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 15.73/15.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 15.73/15.93  thf('128', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k5_xboole_0 @ X1 @ X0)
% 15.73/15.93           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 15.73/15.93      inference('sup+', [status(thm)], ['86', '89'])).
% 15.73/15.93  thf('129', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)],
% 15.73/15.93                ['105', '124', '125', '126', '127', '128'])).
% 15.73/15.93  thf('130', plain,
% 15.73/15.93      (![X0 : $i, X1 : $i]:
% 15.73/15.93         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 15.73/15.93           = (k5_xboole_0 @ X1 @ X0))),
% 15.73/15.93      inference('demod', [status(thm)], ['85', '129'])).
% 15.73/15.93  thf('131', plain,
% 15.73/15.93      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 15.73/15.93      inference('demod', [status(thm)], ['0', '130'])).
% 15.73/15.93  thf('132', plain, ($false), inference('simplify', [status(thm)], ['131'])).
% 15.73/15.93  
% 15.73/15.93  % SZS output end Refutation
% 15.73/15.93  
% 15.73/15.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
