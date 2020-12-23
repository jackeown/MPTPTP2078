%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TXJ5iuwsau

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:01 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 501 expanded)
%              Number of leaves         :   18 ( 181 expanded)
%              Depth                    :   20
%              Number of atoms          :  850 (3840 expanded)
%              Number of equality atoms :   99 ( 493 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
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
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','70'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','73','74','75'])).

thf('77',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','76'])).

thf('78',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('84',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','85'])).

thf('87',plain,(
    $false ),
    inference(simplify,[status(thm)],['86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TXJ5iuwsau
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 729 iterations in 0.347s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(t95_xboole_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k3_xboole_0 @ A @ B ) =
% 0.59/0.80       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ( k3_xboole_0 @ A @ B ) =
% 0.59/0.80          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.59/0.80         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.59/0.80             (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t91_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.80       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.59/0.80           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.59/0.80         != (k5_xboole_0 @ sk_A @ 
% 0.59/0.80             (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.59/0.80      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.80  thf(t40_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.59/0.80           = (k4_xboole_0 @ X8 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.80  thf(d6_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k5_xboole_0 @ A @ B ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X2 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 0.59/0.80              (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.59/0.80              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.59/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.80  thf(t41_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.80       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.80           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf(t1_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.80  thf('10', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.59/0.80           = (k4_xboole_0 @ X8 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.80  thf(t3_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.80  thf('14', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf(t48_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.59/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['13', '16'])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['13', '16'])).
% 0.59/0.80  thf(t51_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.59/0.80       ( A ) ))).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.80           = (X15))),
% 0.59/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.59/0.80           = (k4_xboole_0 @ X8 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.80  thf(t39_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X5 : $i, X6 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['22', '25'])).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['14', '15'])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 0.59/0.80           = (X15))),
% 0.59/0.80      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.59/0.80           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['28', '29'])).
% 0.59/0.80  thf('31', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) = (X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.59/0.80  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('36', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['26', '27', '34', '35'])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X2 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['36', '37'])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['21', '38'])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80           (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X5 : $i, X6 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['43', '44'])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['42', '45'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.80           = (k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80              (k5_xboole_0 @ X0 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['41', '46'])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80           (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['39', '40'])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.59/0.80  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['20', '51', '52'])).
% 0.59/0.80  thf('54', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['17', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X2 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.59/0.80           = (k4_xboole_0 @ X8 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.80  thf('57', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.80           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['55', '56'])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.80           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.59/0.80           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.59/0.80      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.59/0.80           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['54', '59'])).
% 0.59/0.80  thf('61', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf('62', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X2 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.59/0.80  thf('63', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['61', '62'])).
% 0.59/0.80  thf('64', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('65', plain,
% 0.59/0.80      (![X5 : $i, X6 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.59/0.80  thf('67', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['66', '67'])).
% 0.59/0.80  thf('69', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.80  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['60', '68', '69'])).
% 0.59/0.80  thf('71', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.59/0.80           = (k1_xboole_0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['8', '70'])).
% 0.59/0.80  thf('72', plain,
% 0.59/0.80      (![X5 : $i, X6 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.80           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('73', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['71', '72'])).
% 0.59/0.80  thf('74', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.59/0.80  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.59/0.80  thf('76', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k4_xboole_0 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['7', '73', '74', '75'])).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.59/0.80         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('demod', [status(thm)], ['2', '76'])).
% 0.59/0.80  thf('78', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.59/0.80           = (k3_xboole_0 @ X13 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.80  thf('79', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X2 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.59/0.80  thf('80', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.59/0.80              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['78', '79'])).
% 0.59/0.80  thf('81', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.80           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.80  thf('82', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.59/0.80              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.59/0.80      inference('demod', [status(thm)], ['80', '81'])).
% 0.59/0.80  thf('83', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['71', '72'])).
% 0.59/0.80  thf('84', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('85', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.80           = (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.59/0.80  thf('86', plain,
% 0.59/0.80      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['77', '85'])).
% 0.59/0.80  thf('87', plain, ($false), inference('simplify', [status(thm)], ['86'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
