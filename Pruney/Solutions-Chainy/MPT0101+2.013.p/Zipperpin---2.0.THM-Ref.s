%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AzWcqVjTQR

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:56 EST 2020

% Result     : Theorem 14.86s
% Output     : Refutation 14.86s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 170 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  880 (1467 expanded)
%              Number of equality atoms :   95 ( 162 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['59','60','61','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('82',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','80','81'])).

thf('83',plain,(
    $false ),
    inference(simplify,[status(thm)],['82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AzWcqVjTQR
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:09:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.86/15.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.86/15.06  % Solved by: fo/fo7.sh
% 14.86/15.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.86/15.06  % done 5219 iterations in 14.599s
% 14.86/15.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.86/15.06  % SZS output start Refutation
% 14.86/15.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 14.86/15.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.86/15.06  thf(sk_A_type, type, sk_A: $i).
% 14.86/15.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 14.86/15.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.86/15.06  thf(sk_B_type, type, sk_B: $i).
% 14.86/15.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.86/15.06  thf(t94_xboole_1, conjecture,
% 14.86/15.06    (![A:$i,B:$i]:
% 14.86/15.06     ( ( k2_xboole_0 @ A @ B ) =
% 14.86/15.06       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.86/15.06  thf(zf_stmt_0, negated_conjecture,
% 14.86/15.06    (~( ![A:$i,B:$i]:
% 14.86/15.06        ( ( k2_xboole_0 @ A @ B ) =
% 14.86/15.06          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 14.86/15.06    inference('cnf.neg', [status(esa)], [t94_xboole_1])).
% 14.86/15.06  thf('0', plain,
% 14.86/15.06      (((k2_xboole_0 @ sk_A @ sk_B)
% 14.86/15.06         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 14.86/15.06             (k3_xboole_0 @ sk_A @ sk_B)))),
% 14.86/15.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.86/15.06  thf(d6_xboole_0, axiom,
% 14.86/15.06    (![A:$i,B:$i]:
% 14.86/15.06     ( ( k5_xboole_0 @ A @ B ) =
% 14.86/15.06       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 14.86/15.06  thf('1', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf(commutativity_k2_xboole_0, axiom,
% 14.86/15.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 14.86/15.06  thf('2', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('3', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k5_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['1', '2'])).
% 14.86/15.06  thf('4', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf('5', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['3', '4'])).
% 14.86/15.06  thf('6', plain,
% 14.86/15.06      (((k2_xboole_0 @ sk_A @ sk_B)
% 14.86/15.06         != (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 14.86/15.06             (k5_xboole_0 @ sk_A @ sk_B)))),
% 14.86/15.06      inference('demod', [status(thm)], ['0', '5'])).
% 14.86/15.06  thf('7', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['3', '4'])).
% 14.86/15.06  thf(idempotence_k2_xboole_0, axiom,
% 14.86/15.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 14.86/15.06  thf('8', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 14.86/15.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.86/15.06  thf('9', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf('10', plain,
% 14.86/15.06      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['8', '9'])).
% 14.86/15.06  thf(t92_xboole_1, axiom,
% 14.86/15.06    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 14.86/15.06  thf('11', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 14.86/15.06      inference('cnf', [status(esa)], [t92_xboole_1])).
% 14.86/15.06  thf('12', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 14.86/15.06      inference('demod', [status(thm)], ['10', '11'])).
% 14.86/15.06  thf(t48_xboole_1, axiom,
% 14.86/15.06    (![A:$i,B:$i]:
% 14.86/15.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.86/15.06  thf('13', plain,
% 14.86/15.06      (![X11 : $i, X12 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 14.86/15.06           = (k3_xboole_0 @ X11 @ X12))),
% 14.86/15.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.86/15.06  thf('14', plain,
% 14.86/15.06      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['12', '13'])).
% 14.86/15.06  thf(t3_boole, axiom,
% 14.86/15.06    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 14.86/15.06  thf('15', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 14.86/15.06      inference('cnf', [status(esa)], [t3_boole])).
% 14.86/15.06  thf('16', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 14.86/15.06      inference('demod', [status(thm)], ['14', '15'])).
% 14.86/15.06  thf(t52_xboole_1, axiom,
% 14.86/15.06    (![A:$i,B:$i,C:$i]:
% 14.86/15.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 14.86/15.06       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 14.86/15.06  thf('17', plain,
% 14.86/15.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 14.86/15.06              (k3_xboole_0 @ X16 @ X18)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t52_xboole_1])).
% 14.86/15.06  thf('18', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['16', '17'])).
% 14.86/15.06  thf('19', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('20', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 14.86/15.06      inference('demod', [status(thm)], ['18', '19'])).
% 14.86/15.06  thf('21', plain,
% 14.86/15.06      (![X11 : $i, X12 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 14.86/15.06           = (k3_xboole_0 @ X11 @ X12))),
% 14.86/15.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.86/15.06  thf(t39_xboole_1, axiom,
% 14.86/15.06    (![A:$i,B:$i]:
% 14.86/15.06     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 14.86/15.06  thf('22', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('23', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 14.86/15.06      inference('sup+', [status(thm)], ['21', '22'])).
% 14.86/15.06  thf('24', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('25', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('26', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('demod', [status(thm)], ['23', '24', '25'])).
% 14.86/15.06  thf('27', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('28', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 14.86/15.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.86/15.06  thf(t4_xboole_1, axiom,
% 14.86/15.06    (![A:$i,B:$i,C:$i]:
% 14.86/15.06     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 14.86/15.06       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 14.86/15.06  thf('29', plain,
% 14.86/15.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.86/15.06           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.86/15.06  thf('30', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ X1)
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['28', '29'])).
% 14.86/15.06  thf('31', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ X1)
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['27', '30'])).
% 14.86/15.06  thf('32', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 14.86/15.06              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 14.86/15.06      inference('sup+', [status(thm)], ['26', '31'])).
% 14.86/15.06  thf('33', plain,
% 14.86/15.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 14.86/15.06              (k3_xboole_0 @ X16 @ X18)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t52_xboole_1])).
% 14.86/15.06  thf('34', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 14.86/15.06      inference('demod', [status(thm)], ['10', '11'])).
% 14.86/15.06  thf('35', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 14.86/15.06      inference('cnf', [status(esa)], [t3_boole])).
% 14.86/15.06  thf('36', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ X1)
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['27', '30'])).
% 14.86/15.06  thf('37', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('38', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('demod', [status(thm)], ['32', '33', '34', '35', '36', '37'])).
% 14.86/15.06  thf('39', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['20', '38'])).
% 14.86/15.06  thf('40', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf(t41_xboole_1, axiom,
% 14.86/15.06    (![A:$i,B:$i,C:$i]:
% 14.86/15.06     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 14.86/15.06       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 14.86/15.06  thf('41', plain,
% 14.86/15.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 14.86/15.06           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 14.86/15.06  thf('42', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 14.86/15.06           (k4_xboole_0 @ X0 @ X1))
% 14.86/15.06           = (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['40', '41'])).
% 14.86/15.06  thf('43', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.86/15.06           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['39', '42'])).
% 14.86/15.06  thf('44', plain,
% 14.86/15.06      (![X11 : $i, X12 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 14.86/15.06           = (k3_xboole_0 @ X11 @ X12))),
% 14.86/15.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.86/15.06  thf('45', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k3_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('sup+', [status(thm)], ['43', '44'])).
% 14.86/15.06  thf('46', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k3_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['7', '45'])).
% 14.86/15.06  thf('47', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 14.86/15.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.86/15.06  thf('48', plain,
% 14.86/15.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 14.86/15.06           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 14.86/15.06  thf('49', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 14.86/15.06           = (k4_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['47', '48'])).
% 14.86/15.06  thf('50', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf('51', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 14.86/15.06              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 14.86/15.06      inference('sup+', [status(thm)], ['49', '50'])).
% 14.86/15.06  thf('52', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('53', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('54', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('demod', [status(thm)], ['51', '52', '53'])).
% 14.86/15.06  thf('55', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['3', '4'])).
% 14.86/15.06  thf('56', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('demod', [status(thm)], ['54', '55'])).
% 14.86/15.06  thf('57', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('58', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('sup+', [status(thm)], ['56', '57'])).
% 14.86/15.06  thf('59', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 14.86/15.06      inference('sup+', [status(thm)], ['46', '58'])).
% 14.86/15.06  thf('60', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('sup+', [status(thm)], ['3', '4'])).
% 14.86/15.06  thf('61', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('62', plain,
% 14.86/15.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.86/15.06           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.86/15.06  thf('63', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('64', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 14.86/15.06           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['62', '63'])).
% 14.86/15.06  thf('65', plain,
% 14.86/15.06      (![X2 : $i, X3 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ X2 @ X3)
% 14.86/15.06           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 14.86/15.06      inference('cnf', [status(esa)], [d6_xboole_0])).
% 14.86/15.06  thf('66', plain,
% 14.86/15.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 14.86/15.06         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 14.86/15.06           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 14.86/15.06  thf('67', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('68', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 14.86/15.06           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 14.86/15.06           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 14.86/15.06      inference('sup+', [status(thm)], ['66', '67'])).
% 14.86/15.06  thf('69', plain,
% 14.86/15.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.86/15.06           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.86/15.06  thf('70', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('71', plain,
% 14.86/15.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 14.86/15.06           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 14.86/15.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 14.86/15.06  thf('72', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 14.86/15.06      inference('demod', [status(thm)], ['68', '69', '70', '71'])).
% 14.86/15.06  thf('73', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['65', '72'])).
% 14.86/15.06  thf('74', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('75', plain,
% 14.86/15.06      (![X5 : $i, X6 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 14.86/15.06           = (k2_xboole_0 @ X5 @ X6))),
% 14.86/15.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 14.86/15.06  thf('76', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 14.86/15.06      inference('demod', [status(thm)], ['73', '74', '75'])).
% 14.86/15.06  thf('77', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X0)))),
% 14.86/15.06      inference('sup+', [status(thm)], ['64', '76'])).
% 14.86/15.06  thf('78', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 14.86/15.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.86/15.06  thf('79', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))
% 14.86/15.06           = (k2_xboole_0 @ X1 @ X0))),
% 14.86/15.06      inference('demod', [status(thm)], ['77', '78'])).
% 14.86/15.06  thf('80', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]:
% 14.86/15.06         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 14.86/15.06           = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('demod', [status(thm)], ['59', '60', '61', '79'])).
% 14.86/15.06  thf('81', plain,
% 14.86/15.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 14.86/15.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 14.86/15.06  thf('82', plain,
% 14.86/15.06      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 14.86/15.06      inference('demod', [status(thm)], ['6', '80', '81'])).
% 14.86/15.06  thf('83', plain, ($false), inference('simplify', [status(thm)], ['82'])).
% 14.86/15.06  
% 14.86/15.06  % SZS output end Refutation
% 14.86/15.06  
% 14.91/15.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
