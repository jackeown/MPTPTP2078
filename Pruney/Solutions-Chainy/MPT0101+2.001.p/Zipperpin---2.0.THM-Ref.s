%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20XNycqa9k

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:54 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 196 expanded)
%              Number of leaves         :   23 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  746 (1483 expanded)
%              Number of equality atoms :   91 ( 188 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X14 @ X14 ) @ X15 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','36','37'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('46',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X5 @ X4 )
      = ( k5_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','53'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','68','71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.20XNycqa9k
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 960 iterations in 0.522s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(t94_xboole_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k2_xboole_0 @ A @ B ) =
% 0.75/0.97       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i]:
% 0.75/0.97        ( ( k2_xboole_0 @ A @ B ) =
% 0.75/0.97          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 0.75/0.97  thf('0', plain,
% 0.75/0.97      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.75/0.97         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.75/0.97             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(commutativity_k5_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.97  thf('2', plain,
% 0.75/0.97      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.75/0.97         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 0.75/0.97             (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.75/0.97      inference('demod', [status(thm)], ['0', '1'])).
% 0.75/0.97  thf(t91_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.97       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/0.97  thf('3', plain,
% 0.75/0.97      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.97         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.75/0.97           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.97  thf('4', plain,
% 0.75/0.97      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.75/0.97           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['3', '4'])).
% 0.75/0.97  thf('6', plain,
% 0.75/0.97      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.75/0.97         != (k5_xboole_0 @ sk_A @ 
% 0.75/0.97             (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.75/0.97      inference('demod', [status(thm)], ['2', '5'])).
% 0.75/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('7', plain,
% 0.75/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf(t48_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (![X16 : $i, X17 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.97           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.97      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.97  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.97  thf(t46_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.75/0.97      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.75/0.97  thf(t51_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.75/0.97       ( A ) ))).
% 0.75/0.97  thf('11', plain,
% 0.75/0.97      (![X18 : $i, X19 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.75/0.97           = (X18))),
% 0.75/0.97      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 0.75/0.97           k1_xboole_0) = (X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['10', '11'])).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.97  thf('14', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.97  thf(t1_boole, axiom,
% 0.75/0.97    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.97  thf('15', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.75/0.97      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.97  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['14', '15'])).
% 0.75/0.97  thf('17', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.75/0.97  thf('18', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['9', '17'])).
% 0.75/0.97  thf('19', plain,
% 0.75/0.97      (![X18 : $i, X19 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.75/0.97           = (X18))),
% 0.75/0.97      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 0.75/0.97           = (X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['18', '19'])).
% 0.75/0.97  thf(t41_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.97       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.75/0.97           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.97  thf(t39_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (![X8 : $i, X9 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.75/0.97           = (k2_xboole_0 @ X8 @ X9))),
% 0.75/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['8', '23'])).
% 0.75/0.97  thf('25', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['7', '24'])).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.97  thf(idempotence_k2_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.97  thf('27', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.75/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.75/0.98           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.75/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['27', '28'])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.98           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['29', '30'])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 0.75/0.98           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ (k4_xboole_0 @ X14 @ X14) @ X15) = (k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf(t3_boole, axiom,
% 0.75/0.98    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.98  thf('35', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.75/0.98      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.98  thf('36', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['34', '35'])).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['31', '36', '37'])).
% 0.75/0.98  thf(t93_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k2_xboole_0 @ A @ B ) =
% 0.75/0.98       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X25 @ X26)
% 0.75/0.98           = (k2_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 0.75/0.98              (k3_xboole_0 @ X25 @ X26)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X25 : $i, X26 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X25 @ X26)
% 0.75/0.98           = (k2_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ 
% 0.75/0.98              (k5_xboole_0 @ X25 @ X26)))),
% 0.75/0.98      inference('demod', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.75/0.98              (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.75/0.98      inference('sup+', [status(thm)], ['38', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.75/0.98           = (k2_xboole_0 @ X8 @ X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.98  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['14', '15'])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X0 @ X1)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.75/0.98  thf(t92_xboole_1, axiom,
% 0.75/0.98    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.75/0.98  thf('46', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 0.75/0.98           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['46', '47'])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf(t5_boole, axiom,
% 0.75/0.98    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.98  thf('50', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.75/0.98      inference('cnf', [status(esa)], [t5_boole])).
% 0.75/0.98  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['49', '50'])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['48', '51'])).
% 0.75/0.98  thf('53', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.98           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['45', '52'])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['26', '53'])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['25', '54'])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.98           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.75/0.98           = (k3_xboole_0 @ X16 @ X17))),
% 0.75/0.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['57', '58'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.75/0.98           = (X18))),
% 0.75/0.98      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['9', '17'])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.75/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['60', '61'])).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.75/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('demod', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['59', '64'])).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.98           = (k4_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('sup+', [status(thm)], ['56', '65'])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i]: ((k5_xboole_0 @ X5 @ X4) = (k5_xboole_0 @ X4 @ X5))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['55', '66', '67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k4_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['26', '53'])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['48', '51'])).
% 0.75/0.98  thf('71', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k2_xboole_0 @ X1 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['69', '70'])).
% 0.75/0.98  thf('72', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.98  thf('73', plain,
% 0.75/0.98      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.98      inference('demod', [status(thm)], ['6', '68', '71', '72'])).
% 0.75/0.98  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
