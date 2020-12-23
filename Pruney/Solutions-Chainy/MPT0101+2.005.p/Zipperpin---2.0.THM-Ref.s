%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IntT2yHYZJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:55 EST 2020

% Result     : Theorem 25.35s
% Output     : Refutation 25.35s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 519 expanded)
%              Number of leaves         :   22 ( 191 expanded)
%              Depth                    :   23
%              Number of atoms          : 1455 (4028 expanded)
%              Number of equality atoms :  162 ( 511 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','26'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','42'])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['62','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22','23','26'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['75','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['61','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('96',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','94','99'])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('114',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('118',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('122',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('125',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k2_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('140',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k4_xboole_0 @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['116','135','138','139','140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','143'])).

thf('145',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','144'])).

thf('146',plain,(
    $false ),
    inference(simplify,[status(thm)],['145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IntT2yHYZJ
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 25.35/25.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 25.35/25.57  % Solved by: fo/fo7.sh
% 25.35/25.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 25.35/25.57  % done 7841 iterations in 25.086s
% 25.35/25.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 25.35/25.57  % SZS output start Refutation
% 25.35/25.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 25.35/25.57  thf(sk_B_type, type, sk_B: $i).
% 25.35/25.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 25.35/25.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 25.35/25.57  thf(sk_A_type, type, sk_A: $i).
% 25.35/25.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 25.35/25.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 25.35/25.57  thf(t94_xboole_1, conjecture,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k2_xboole_0 @ A @ B ) =
% 25.35/25.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 25.35/25.57  thf(zf_stmt_0, negated_conjecture,
% 25.35/25.57    (~( ![A:$i,B:$i]:
% 25.35/25.57        ( ( k2_xboole_0 @ A @ B ) =
% 25.35/25.57          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 25.35/25.57    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 25.35/25.57  thf('0', plain,
% 25.35/25.57      (((k2_xboole_0 @ sk_A @ sk_B)
% 25.35/25.57         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 25.35/25.57             (k3_xboole_0 @ sk_A @ sk_B)))),
% 25.35/25.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 25.35/25.57  thf(d6_xboole_0, axiom,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k5_xboole_0 @ A @ B ) =
% 25.35/25.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 25.35/25.57  thf('1', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf(commutativity_k2_xboole_0, axiom,
% 25.35/25.57    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 25.35/25.57  thf('2', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('3', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k5_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['1', '2'])).
% 25.35/25.57  thf('4', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('5', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['3', '4'])).
% 25.35/25.57  thf('6', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf(t48_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 25.35/25.57  thf('7', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf(t41_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i,C:$i]:
% 25.35/25.57     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 25.35/25.57       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 25.35/25.57  thf('8', plain,
% 25.35/25.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 25.35/25.57           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 25.35/25.57  thf('9', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['7', '8'])).
% 25.35/25.57  thf(t49_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i,C:$i]:
% 25.35/25.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 25.35/25.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 25.35/25.57  thf('10', plain,
% 25.35/25.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 25.35/25.57           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 25.35/25.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.35/25.57  thf('11', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 25.35/25.57      inference('demod', [status(thm)], ['9', '10'])).
% 25.35/25.57  thf('12', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['6', '11'])).
% 25.35/25.57  thf('13', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('14', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['12', '13'])).
% 25.35/25.57  thf(commutativity_k3_xboole_0, axiom,
% 25.35/25.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 25.35/25.57  thf('15', plain,
% 25.35/25.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.35/25.57  thf(t47_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 25.35/25.57  thf('16', plain,
% 25.35/25.57      (![X13 : $i, X14 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 25.35/25.57           = (k4_xboole_0 @ X13 @ X14))),
% 25.35/25.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 25.35/25.57  thf('17', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('sup+', [status(thm)], ['15', '16'])).
% 25.35/25.57  thf(t51_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 25.35/25.57       ( A ) ))).
% 25.35/25.57  thf('18', plain,
% 25.35/25.57      (![X24 : $i, X25 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 25.35/25.57           = (X24))),
% 25.35/25.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 25.35/25.57  thf(t4_boole, axiom,
% 25.35/25.57    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 25.35/25.57  thf('19', plain,
% 25.35/25.57      (![X20 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_boole])).
% 25.35/25.57  thf('20', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('21', plain,
% 25.35/25.57      (![X0 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['19', '20'])).
% 25.35/25.57  thf(t5_boole, axiom,
% 25.35/25.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 25.35/25.57  thf('22', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 25.35/25.57      inference('cnf', [status(esa)], [t5_boole])).
% 25.35/25.57  thf('23', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('24', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf(t1_boole, axiom,
% 25.35/25.57    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 25.35/25.57  thf('25', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 25.35/25.57      inference('cnf', [status(esa)], [t1_boole])).
% 25.35/25.57  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['24', '25'])).
% 25.35/25.57  thf('27', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['21', '22', '23', '26'])).
% 25.35/25.57  thf('28', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('29', plain,
% 25.35/25.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['27', '28'])).
% 25.35/25.57  thf(t2_boole, axiom,
% 25.35/25.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 25.35/25.57  thf('30', plain,
% 25.35/25.57      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 25.35/25.57      inference('cnf', [status(esa)], [t2_boole])).
% 25.35/25.57  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['29', '30'])).
% 25.35/25.57  thf('32', plain,
% 25.35/25.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 25.35/25.57           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 25.35/25.57  thf('33', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['31', '32'])).
% 25.35/25.57  thf('34', plain,
% 25.35/25.57      (![X20 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_boole])).
% 25.35/25.57  thf('35', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['33', '34'])).
% 25.35/25.57  thf('36', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['18', '35'])).
% 25.35/25.57  thf('37', plain,
% 25.35/25.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 25.35/25.57           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 25.35/25.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.35/25.57  thf('38', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['36', '37'])).
% 25.35/25.57  thf('39', plain,
% 25.35/25.57      (![X13 : $i, X14 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 25.35/25.57           = (k4_xboole_0 @ X13 @ X14))),
% 25.35/25.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 25.35/25.57  thf('40', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 25.35/25.57           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['38', '39'])).
% 25.35/25.57  thf('41', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['21', '22', '23', '26'])).
% 25.35/25.57  thf('42', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['40', '41'])).
% 25.35/25.57  thf('43', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['17', '42'])).
% 25.35/25.57  thf('44', plain,
% 25.35/25.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 25.35/25.57           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 25.35/25.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.35/25.57  thf('45', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('46', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 25.35/25.57  thf('47', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ X0)
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['14', '46'])).
% 25.35/25.57  thf('48', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('49', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['47', '48'])).
% 25.35/25.57  thf('50', plain,
% 25.35/25.57      (![X13 : $i, X14 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 25.35/25.57           = (k4_xboole_0 @ X13 @ X14))),
% 25.35/25.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 25.35/25.57  thf('51', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['49', '50'])).
% 25.35/25.57  thf('52', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('sup+', [status(thm)], ['5', '51'])).
% 25.35/25.57  thf('53', plain,
% 25.35/25.57      (![X13 : $i, X14 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 25.35/25.57           = (k4_xboole_0 @ X13 @ X14))),
% 25.35/25.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 25.35/25.57  thf('54', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('55', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 25.35/25.57              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['53', '54'])).
% 25.35/25.57  thf('56', plain,
% 25.35/25.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 25.35/25.57           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 25.35/25.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 25.35/25.57  thf('57', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['36', '37'])).
% 25.35/25.57  thf('58', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['24', '25'])).
% 25.35/25.57  thf('60', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 25.35/25.57  thf('61', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['52', '60'])).
% 25.35/25.57  thf('62', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k4_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('sup+', [status(thm)], ['15', '16'])).
% 25.35/25.57  thf('63', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('64', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('65', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 25.35/25.57              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['63', '64'])).
% 25.35/25.57  thf('66', plain,
% 25.35/25.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 25.35/25.57           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 25.35/25.57  thf('67', plain,
% 25.35/25.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 25.35/25.57           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 25.35/25.57  thf('68', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['29', '30'])).
% 25.35/25.57  thf('69', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 25.35/25.57           = (k1_xboole_0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['67', '68'])).
% 25.35/25.57  thf(t39_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i]:
% 25.35/25.57     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 25.35/25.57  thf('70', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('71', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['69', '70'])).
% 25.35/25.57  thf('72', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['24', '25'])).
% 25.35/25.57  thf('74', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k3_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['65', '66', '71', '72', '73'])).
% 25.35/25.57  thf('75', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['62', '74'])).
% 25.35/25.57  thf('76', plain,
% 25.35/25.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.35/25.57  thf('77', plain,
% 25.35/25.57      (![X24 : $i, X25 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 25.35/25.57           = (X24))),
% 25.35/25.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 25.35/25.57  thf('78', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['76', '77'])).
% 25.35/25.57  thf('79', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('80', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['69', '70'])).
% 25.35/25.57  thf('81', plain,
% 25.35/25.57      (![X15 : $i, X16 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 25.35/25.57           = (k3_xboole_0 @ X15 @ X16))),
% 25.35/25.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 25.35/25.57  thf('82', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 25.35/25.57           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['80', '81'])).
% 25.35/25.57  thf('83', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['21', '22', '23', '26'])).
% 25.35/25.57  thf('84', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['82', '83'])).
% 25.35/25.57  thf('85', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['79', '84'])).
% 25.35/25.57  thf('86', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ X0)
% 25.35/25.57           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['78', '85'])).
% 25.35/25.57  thf('87', plain,
% 25.35/25.57      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 25.35/25.57  thf('88', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X1 @ X0)
% 25.35/25.57           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['86', '87'])).
% 25.35/25.57  thf('89', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k3_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('demod', [status(thm)], ['75', '88'])).
% 25.35/25.57  thf('90', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k3_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 25.35/25.57      inference('demod', [status(thm)], ['61', '89'])).
% 25.35/25.57  thf('91', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['40', '41'])).
% 25.35/25.57  thf('92', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('93', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['91', '92'])).
% 25.35/25.57  thf('94', plain,
% 25.35/25.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 25.35/25.57         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 25.35/25.57           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t41_xboole_1])).
% 25.35/25.57  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 25.35/25.57      inference('demod', [status(thm)], ['29', '30'])).
% 25.35/25.57  thf('96', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('97', plain,
% 25.35/25.57      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['95', '96'])).
% 25.35/25.57  thf('98', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 25.35/25.57      inference('cnf', [status(esa)], [t1_boole])).
% 25.35/25.57  thf('99', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['97', '98'])).
% 25.35/25.57  thf('100', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['93', '94', '99'])).
% 25.35/25.57  thf('101', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('102', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('sup+', [status(thm)], ['100', '101'])).
% 25.35/25.57  thf('103', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['90', '102'])).
% 25.35/25.57  thf('104', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('105', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['3', '4'])).
% 25.35/25.57  thf('106', plain,
% 25.35/25.57      (![X4 : $i, X5 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ X4 @ X5)
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 25.35/25.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 25.35/25.57  thf('107', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['97', '98'])).
% 25.35/25.57  thf(t4_xboole_1, axiom,
% 25.35/25.57    (![A:$i,B:$i,C:$i]:
% 25.35/25.57     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 25.35/25.57       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 25.35/25.57  thf('108', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('109', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['107', '108'])).
% 25.35/25.57  thf('110', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['106', '109'])).
% 25.35/25.57  thf('111', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('112', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['110', '111'])).
% 25.35/25.57  thf('113', plain,
% 25.35/25.57      (![X24 : $i, X25 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 25.35/25.57           = (X24))),
% 25.35/25.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 25.35/25.57  thf('114', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('115', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ 
% 25.35/25.57              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['113', '114'])).
% 25.35/25.57  thf('116', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 25.35/25.57              (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 25.35/25.57      inference('sup+', [status(thm)], ['112', '115'])).
% 25.35/25.57  thf('117', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['33', '34'])).
% 25.35/25.57  thf('118', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('119', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 25.35/25.57           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['117', '118'])).
% 25.35/25.57  thf('120', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('121', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 25.35/25.57      inference('cnf', [status(esa)], [t1_boole])).
% 25.35/25.57  thf('122', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('123', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 25.35/25.57  thf('124', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('125', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('126', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 25.35/25.57           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['124', '125'])).
% 25.35/25.57  thf('127', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('128', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 25.35/25.57           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 25.35/25.57      inference('demod', [status(thm)], ['126', '127'])).
% 25.35/25.57  thf('129', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['123', '128'])).
% 25.35/25.57  thf('130', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['82', '83'])).
% 25.35/25.57  thf('131', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 25.35/25.57           = (X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['76', '77'])).
% 25.35/25.57  thf('132', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('sup+', [status(thm)], ['130', '131'])).
% 25.35/25.57  thf('133', plain,
% 25.35/25.57      (![X8 : $i, X9 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 25.35/25.57           = (k2_xboole_0 @ X8 @ X9))),
% 25.35/25.57      inference('cnf', [status(esa)], [t39_xboole_1])).
% 25.35/25.57  thf('134', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['132', '133'])).
% 25.35/25.57  thf('135', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X1 @ X0)
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)], ['129', '134'])).
% 25.35/25.57  thf('136', plain,
% 25.35/25.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X23)
% 25.35/25.57           = (k2_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 25.35/25.57      inference('cnf', [status(esa)], [t4_xboole_1])).
% 25.35/25.57  thf('137', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('138', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 25.35/25.57           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['136', '137'])).
% 25.35/25.57  thf('139', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('140', plain,
% 25.35/25.57      (![X24 : $i, X25 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ (k4_xboole_0 @ X24 @ X25))
% 25.35/25.57           = (X24))),
% 25.35/25.57      inference('cnf', [status(esa)], [t51_xboole_1])).
% 25.35/25.57  thf('141', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 25.35/25.57      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 25.35/25.57  thf('142', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X0 @ X1)
% 25.35/25.57           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('demod', [status(thm)],
% 25.35/25.57                ['116', '135', '138', '139', '140', '141'])).
% 25.35/25.57  thf('143', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k2_xboole_0 @ X1 @ X0)
% 25.35/25.57           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 25.35/25.57      inference('sup+', [status(thm)], ['105', '142'])).
% 25.35/25.57  thf('144', plain,
% 25.35/25.57      (![X0 : $i, X1 : $i]:
% 25.35/25.57         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 25.35/25.57           = (k2_xboole_0 @ X1 @ X0))),
% 25.35/25.57      inference('demod', [status(thm)], ['103', '104', '143'])).
% 25.35/25.57  thf('145', plain,
% 25.35/25.57      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 25.35/25.57      inference('demod', [status(thm)], ['0', '144'])).
% 25.35/25.57  thf('146', plain, ($false), inference('simplify', [status(thm)], ['145'])).
% 25.35/25.57  
% 25.35/25.57  % SZS output end Refutation
% 25.35/25.57  
% 25.35/25.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
