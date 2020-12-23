%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A1VRfoOacp

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:54 EST 2020

% Result     : Theorem 35.23s
% Output     : Refutation 35.23s
% Verified   : 
% Statistics : Number of formulae       :  130 (1065 expanded)
%              Number of leaves         :   19 ( 376 expanded)
%              Depth                    :   18
%              Number of atoms          : 1161 (8746 expanded)
%              Number of equality atoms :  122 (1057 expanded)
%              Maximal formula depth    :   11 (   7 average)

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

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('76',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','67','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','67','78','79','80'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','67','78','79','80'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','81','86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('100',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['97','102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('108',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','106','107'])).

thf('109',plain,(
    $false ),
    inference(simplify,[status(thm)],['108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A1VRfoOacp
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 35.23/35.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 35.23/35.47  % Solved by: fo/fo7.sh
% 35.23/35.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.23/35.47  % done 12697 iterations in 35.015s
% 35.23/35.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 35.23/35.47  % SZS output start Refutation
% 35.23/35.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 35.23/35.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 35.23/35.47  thf(sk_A_type, type, sk_A: $i).
% 35.23/35.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 35.23/35.47  thf(sk_B_type, type, sk_B: $i).
% 35.23/35.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 35.23/35.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 35.23/35.47  thf(t94_xboole_1, conjecture,
% 35.23/35.47    (![A:$i,B:$i]:
% 35.23/35.47     ( ( k2_xboole_0 @ A @ B ) =
% 35.23/35.47       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 35.23/35.47  thf(zf_stmt_0, negated_conjecture,
% 35.23/35.47    (~( ![A:$i,B:$i]:
% 35.23/35.47        ( ( k2_xboole_0 @ A @ B ) =
% 35.23/35.47          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 35.23/35.47    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 35.23/35.47  thf('0', plain,
% 35.23/35.47      (((k2_xboole_0 @ sk_A @ sk_B)
% 35.23/35.47         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 35.23/35.47             (k3_xboole_0 @ sk_A @ sk_B)))),
% 35.23/35.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.23/35.47  thf(d6_xboole_0, axiom,
% 35.23/35.47    (![A:$i,B:$i]:
% 35.23/35.47     ( ( k5_xboole_0 @ A @ B ) =
% 35.23/35.47       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 35.23/35.47  thf('1', plain,
% 35.23/35.47      (![X4 : $i, X5 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ X4 @ X5)
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 35.23/35.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 35.23/35.47  thf(commutativity_k2_xboole_0, axiom,
% 35.23/35.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 35.23/35.47  thf('2', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.47  thf('3', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 35.23/35.47           = (k5_xboole_0 @ X1 @ X0))),
% 35.23/35.47      inference('sup+', [status(thm)], ['1', '2'])).
% 35.23/35.47  thf('4', plain,
% 35.23/35.47      (![X4 : $i, X5 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ X4 @ X5)
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 35.23/35.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 35.23/35.47  thf('5', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 35.23/35.47      inference('sup+', [status(thm)], ['3', '4'])).
% 35.23/35.47  thf('6', plain,
% 35.23/35.47      (((k2_xboole_0 @ sk_A @ sk_B)
% 35.23/35.47         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 35.23/35.47             (k5_xboole_0 @ sk_A @ sk_B)))),
% 35.23/35.47      inference('demod', [status(thm)], ['0', '5'])).
% 35.23/35.47  thf(t48_xboole_1, axiom,
% 35.23/35.47    (![A:$i,B:$i]:
% 35.23/35.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 35.23/35.47  thf('7', plain,
% 35.23/35.47      (![X15 : $i, X16 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 35.23/35.47           = (k3_xboole_0 @ X15 @ X16))),
% 35.23/35.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.23/35.47  thf(t39_xboole_1, axiom,
% 35.23/35.47    (![A:$i,B:$i]:
% 35.23/35.47     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 35.23/35.47  thf('8', plain,
% 35.23/35.47      (![X7 : $i, X8 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 35.23/35.47           = (k2_xboole_0 @ X7 @ X8))),
% 35.23/35.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.23/35.47  thf('9', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 35.23/35.47      inference('sup+', [status(thm)], ['7', '8'])).
% 35.23/35.47  thf('10', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.47  thf('11', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.47  thf('12', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 35.23/35.47           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.47      inference('demod', [status(thm)], ['9', '10', '11'])).
% 35.23/35.47  thf(t41_xboole_1, axiom,
% 35.23/35.47    (![A:$i,B:$i,C:$i]:
% 35.23/35.47     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 35.23/35.47       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 35.23/35.47  thf('13', plain,
% 35.23/35.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.47  thf('14', plain,
% 35.23/35.47      (![X4 : $i, X5 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ X4 @ X5)
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 35.23/35.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 35.23/35.47  thf('15', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 35.23/35.47              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 35.23/35.47      inference('sup+', [status(thm)], ['13', '14'])).
% 35.23/35.47  thf('16', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 35.23/35.47           (k4_xboole_0 @ X1 @ X0))
% 35.23/35.47           = (k2_xboole_0 @ 
% 35.23/35.47              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 35.23/35.47              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.23/35.47               (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))))),
% 35.23/35.47      inference('sup+', [status(thm)], ['12', '15'])).
% 35.23/35.47  thf('17', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 35.23/35.47      inference('sup+', [status(thm)], ['3', '4'])).
% 35.23/35.47  thf('18', plain,
% 35.23/35.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.47  thf('19', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.23/35.47           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 35.23/35.47           = (k2_xboole_0 @ 
% 35.23/35.47              (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 35.23/35.47              (k4_xboole_0 @ X1 @ 
% 35.23/35.47               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))))),
% 35.23/35.47      inference('demod', [status(thm)], ['16', '17', '18'])).
% 35.23/35.47  thf(idempotence_k2_xboole_0, axiom,
% 35.23/35.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 35.23/35.47  thf('20', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 35.23/35.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.23/35.47  thf('21', plain,
% 35.23/35.47      (![X4 : $i, X5 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ X4 @ X5)
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 35.23/35.47      inference('cnf', [status(esa)], [d6_xboole_0])).
% 35.23/35.47  thf('22', plain,
% 35.23/35.47      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 35.23/35.47      inference('sup+', [status(thm)], ['20', '21'])).
% 35.23/35.47  thf(t92_xboole_1, axiom,
% 35.23/35.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 35.23/35.47  thf('23', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 35.23/35.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 35.23/35.47  thf('24', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 35.23/35.47      inference('demod', [status(thm)], ['22', '23'])).
% 35.23/35.47  thf('25', plain,
% 35.23/35.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.47  thf('26', plain,
% 35.23/35.47      (![X7 : $i, X8 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 35.23/35.47           = (k2_xboole_0 @ X7 @ X8))),
% 35.23/35.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.23/35.47  thf('27', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 35.23/35.47           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 35.23/35.47      inference('sup+', [status(thm)], ['25', '26'])).
% 35.23/35.47  thf('28', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 35.23/35.47           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 35.23/35.47      inference('sup+', [status(thm)], ['24', '27'])).
% 35.23/35.47  thf('29', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 35.23/35.47      inference('demod', [status(thm)], ['22', '23'])).
% 35.23/35.47  thf('30', plain,
% 35.23/35.47      (![X7 : $i, X8 : $i]:
% 35.23/35.47         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 35.23/35.47           = (k2_xboole_0 @ X7 @ X8))),
% 35.23/35.47      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.23/35.47  thf('31', plain,
% 35.23/35.47      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 35.23/35.47      inference('sup+', [status(thm)], ['29', '30'])).
% 35.23/35.47  thf('32', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 35.23/35.47      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 35.23/35.47  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 35.23/35.47      inference('demod', [status(thm)], ['31', '32'])).
% 35.23/35.47  thf('34', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.47  thf(t40_xboole_1, axiom,
% 35.23/35.47    (![A:$i,B:$i]:
% 35.23/35.47     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 35.23/35.47  thf('35', plain,
% 35.23/35.47      (![X10 : $i, X11 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 35.23/35.47           = (k4_xboole_0 @ X10 @ X11))),
% 35.23/35.47      inference('cnf', [status(esa)], [t40_xboole_1])).
% 35.23/35.47  thf('36', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 35.23/35.47           = (k4_xboole_0 @ X0 @ X1))),
% 35.23/35.47      inference('sup+', [status(thm)], ['34', '35'])).
% 35.23/35.47  thf('37', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.47      inference('demod', [status(thm)], ['28', '33', '36'])).
% 35.23/35.47  thf('38', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.23/35.47           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 35.23/35.47           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 35.23/35.47              (k4_xboole_0 @ X1 @ 
% 35.23/35.47               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))))),
% 35.23/35.47      inference('demod', [status(thm)], ['19', '37'])).
% 35.23/35.47  thf('39', plain,
% 35.23/35.47      (![X15 : $i, X16 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 35.23/35.47           = (k3_xboole_0 @ X15 @ X16))),
% 35.23/35.47      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.23/35.47  thf('40', plain,
% 35.23/35.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.47  thf('41', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 35.23/35.47           = (k4_xboole_0 @ X2 @ 
% 35.23/35.47              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 35.23/35.47      inference('sup+', [status(thm)], ['39', '40'])).
% 35.23/35.47  thf('42', plain,
% 35.23/35.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.47         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.47           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.47  thf('43', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.23/35.47         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 35.23/35.47           = (k4_xboole_0 @ X2 @ 
% 35.23/35.47              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 35.23/35.47      inference('demod', [status(thm)], ['41', '42'])).
% 35.23/35.47  thf('44', plain,
% 35.23/35.47      (![X0 : $i, X1 : $i]:
% 35.23/35.47         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 35.23/35.47           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))
% 35.23/35.48           = (k4_xboole_0 @ X0 @ 
% 35.23/35.48              (k5_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 35.23/35.48               (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))))),
% 35.23/35.48      inference('sup+', [status(thm)], ['38', '43'])).
% 35.23/35.48  thf('45', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['22', '23'])).
% 35.23/35.48  thf('46', plain,
% 35.23/35.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 35.23/35.48           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 35.23/35.48      inference('cnf', [status(esa)], [t41_xboole_1])).
% 35.23/35.48  thf('47', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0)
% 35.23/35.48           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 35.23/35.48      inference('sup+', [status(thm)], ['45', '46'])).
% 35.23/35.48  thf('48', plain,
% 35.23/35.48      (![X7 : $i, X8 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 35.23/35.48           = (k2_xboole_0 @ X7 @ X8))),
% 35.23/35.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.23/35.48  thf('49', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 35.23/35.48      inference('demod', [status(thm)], ['47', '48'])).
% 35.23/35.48  thf('50', plain,
% 35.23/35.48      (![X7 : $i, X8 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 35.23/35.48           = (k2_xboole_0 @ X7 @ X8))),
% 35.23/35.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 35.23/35.48  thf('51', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 35.23/35.48           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 35.23/35.48      inference('sup+', [status(thm)], ['49', '50'])).
% 35.23/35.48  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['31', '32'])).
% 35.23/35.48  thf('53', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.48  thf('54', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X1 @ X0)
% 35.23/35.48           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['51', '52', '53'])).
% 35.23/35.48  thf(t93_xboole_1, axiom,
% 35.23/35.48    (![A:$i,B:$i]:
% 35.23/35.48     ( ( k2_xboole_0 @ A @ B ) =
% 35.23/35.48       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 35.23/35.48  thf('55', plain,
% 35.23/35.48      (![X18 : $i, X19 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X18 @ X19)
% 35.23/35.48           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 35.23/35.48              (k3_xboole_0 @ X18 @ X19)))),
% 35.23/35.48      inference('cnf', [status(esa)], [t93_xboole_1])).
% 35.23/35.48  thf('56', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.48  thf('57', plain,
% 35.23/35.48      (![X18 : $i, X19 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X18 @ X19)
% 35.23/35.48           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 35.23/35.48              (k5_xboole_0 @ X18 @ X19)))),
% 35.23/35.48      inference('demod', [status(thm)], ['55', '56'])).
% 35.23/35.48  thf('58', plain,
% 35.23/35.48      (![X10 : $i, X11 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 35.23/35.48           = (k4_xboole_0 @ X10 @ X11))),
% 35.23/35.48      inference('cnf', [status(esa)], [t40_xboole_1])).
% 35.23/35.48  thf('59', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['57', '58'])).
% 35.23/35.48  thf('60', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 35.23/35.48           (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 35.23/35.48           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 35.23/35.48              (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 35.23/35.48      inference('sup+', [status(thm)], ['54', '59'])).
% 35.23/35.48  thf('61', plain,
% 35.23/35.48      (![X10 : $i, X11 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 35.23/35.48           = (k4_xboole_0 @ X10 @ X11))),
% 35.23/35.48      inference('cnf', [status(esa)], [t40_xboole_1])).
% 35.23/35.48  thf('62', plain,
% 35.23/35.48      (![X4 : $i, X5 : $i]:
% 35.23/35.48         ((k5_xboole_0 @ X4 @ X5)
% 35.23/35.48           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 35.23/35.48      inference('cnf', [status(esa)], [d6_xboole_0])).
% 35.23/35.48  thf('63', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 35.23/35.48           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 35.23/35.48              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 35.23/35.48      inference('sup+', [status(thm)], ['61', '62'])).
% 35.23/35.48  thf('64', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 35.23/35.48      inference('sup+', [status(thm)], ['3', '4'])).
% 35.23/35.48  thf('65', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 35.23/35.48      inference('demod', [status(thm)], ['47', '48'])).
% 35.23/35.48  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['31', '32'])).
% 35.23/35.48  thf('67', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k4_xboole_0 @ X1 @ X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 35.23/35.48  thf('68', plain,
% 35.23/35.48      (![X10 : $i, X11 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 35.23/35.48           = (k4_xboole_0 @ X10 @ X11))),
% 35.23/35.48      inference('cnf', [status(esa)], [t40_xboole_1])).
% 35.23/35.48  thf('69', plain,
% 35.23/35.48      (![X15 : $i, X16 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 35.23/35.48           = (k3_xboole_0 @ X15 @ X16))),
% 35.23/35.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.23/35.48  thf('70', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 35.23/35.48      inference('sup+', [status(thm)], ['68', '69'])).
% 35.23/35.48  thf(commutativity_k3_xboole_0, axiom,
% 35.23/35.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 35.23/35.48  thf('71', plain,
% 35.23/35.48      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 35.23/35.48  thf('72', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['70', '71'])).
% 35.23/35.48  thf('73', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 35.23/35.48      inference('demod', [status(thm)], ['47', '48'])).
% 35.23/35.48  thf('74', plain,
% 35.23/35.48      (![X15 : $i, X16 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 35.23/35.48           = (k3_xboole_0 @ X15 @ X16))),
% 35.23/35.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.23/35.48  thf('75', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 35.23/35.48           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['73', '74'])).
% 35.23/35.48  thf(t3_boole, axiom,
% 35.23/35.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 35.23/35.48  thf('76', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 35.23/35.48      inference('cnf', [status(esa)], [t3_boole])).
% 35.23/35.48  thf('77', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['75', '76'])).
% 35.23/35.48  thf('78', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['72', '77'])).
% 35.23/35.48  thf('79', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['75', '76'])).
% 35.23/35.48  thf('80', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k4_xboole_0 @ X1 @ X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 35.23/35.48  thf('81', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['60', '67', '78', '79', '80'])).
% 35.23/35.48  thf('82', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['60', '67', '78', '79', '80'])).
% 35.23/35.48  thf('83', plain,
% 35.23/35.48      (![X15 : $i, X16 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 35.23/35.48           = (k3_xboole_0 @ X15 @ X16))),
% 35.23/35.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 35.23/35.48  thf('84', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k4_xboole_0 @ X0 @ X0)
% 35.23/35.48           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['82', '83'])).
% 35.23/35.48  thf('85', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['22', '23'])).
% 35.23/35.48  thf('86', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['84', '85'])).
% 35.23/35.48  thf('87', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 35.23/35.48      inference('cnf', [status(esa)], [t3_boole])).
% 35.23/35.48  thf('88', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['60', '67', '78', '79', '80'])).
% 35.23/35.48  thf('89', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['84', '85'])).
% 35.23/35.48  thf('90', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 35.23/35.48      inference('cnf', [status(esa)], [t3_boole])).
% 35.23/35.48  thf('91', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k3_xboole_0 @ X0 @ X1)
% 35.23/35.48           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 35.23/35.48      inference('demod', [status(thm)],
% 35.23/35.48                ['44', '81', '86', '87', '88', '89', '90'])).
% 35.23/35.48  thf('92', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['84', '85'])).
% 35.23/35.48  thf('93', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0)
% 35.23/35.48           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['91', '92'])).
% 35.23/35.48  thf('94', plain,
% 35.23/35.48      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 35.23/35.48  thf('95', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k1_xboole_0)
% 35.23/35.48           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['93', '94'])).
% 35.23/35.48  thf('96', plain,
% 35.23/35.48      (![X18 : $i, X19 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X18 @ X19)
% 35.23/35.48           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 35.23/35.48              (k5_xboole_0 @ X18 @ X19)))),
% 35.23/35.48      inference('demod', [status(thm)], ['55', '56'])).
% 35.23/35.48  thf('97', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 35.23/35.48           = (k2_xboole_0 @ k1_xboole_0 @ 
% 35.23/35.48              (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))))),
% 35.23/35.48      inference('sup+', [status(thm)], ['95', '96'])).
% 35.23/35.48  thf('98', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 35.23/35.48      inference('sup+', [status(thm)], ['3', '4'])).
% 35.23/35.48  thf('99', plain,
% 35.23/35.48      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 35.23/35.48  thf('100', plain,
% 35.23/35.48      (![X18 : $i, X19 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X18 @ X19)
% 35.23/35.48           = (k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ 
% 35.23/35.48              (k5_xboole_0 @ X18 @ X19)))),
% 35.23/35.48      inference('demod', [status(thm)], ['55', '56'])).
% 35.23/35.48  thf('101', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X0 @ X1)
% 35.23/35.48           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['99', '100'])).
% 35.23/35.48  thf('102', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X0 @ X1)
% 35.23/35.48           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('sup+', [status(thm)], ['98', '101'])).
% 35.23/35.48  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 35.23/35.48      inference('demod', [status(thm)], ['31', '32'])).
% 35.23/35.48  thf('104', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.48  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 35.23/35.48      inference('sup+', [status(thm)], ['103', '104'])).
% 35.23/35.48  thf('106', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]:
% 35.23/35.48         ((k2_xboole_0 @ X0 @ X1)
% 35.23/35.48           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 35.23/35.48      inference('demod', [status(thm)], ['97', '102', '105'])).
% 35.23/35.48  thf('107', plain,
% 35.23/35.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 35.23/35.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 35.23/35.48  thf('108', plain,
% 35.23/35.48      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 35.23/35.48      inference('demod', [status(thm)], ['6', '106', '107'])).
% 35.23/35.48  thf('109', plain, ($false), inference('simplify', [status(thm)], ['108'])).
% 35.23/35.48  
% 35.23/35.48  % SZS output end Refutation
% 35.23/35.48  
% 35.23/35.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
