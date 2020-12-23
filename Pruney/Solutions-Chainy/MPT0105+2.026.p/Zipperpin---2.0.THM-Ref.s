%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M6l3gR5C6M

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:08 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 896 expanded)
%              Number of leaves         :   18 ( 305 expanded)
%              Depth                    :   24
%              Number of atoms          :  986 (6895 expanded)
%              Number of equality atoms :  117 ( 888 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','12'])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','96'])).

thf('98',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M6l3gR5C6M
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 1062 iterations in 0.581s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(t98_xboole_1, conjecture,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i,B:$i]:
% 0.83/1.04        ( ( k2_xboole_0 @ A @ B ) =
% 0.83/1.04          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.83/1.04  thf('0', plain,
% 0.83/1.04      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.83/1.04         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t48_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X10 : $i, X11 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.04           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.04  thf(t41_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.83/1.04       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.04           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.04  thf(t3_boole, axiom,
% 0.83/1.04    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.04  thf('3', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.04  thf('4', plain,
% 0.83/1.04      (![X10 : $i, X11 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.04           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['3', '4'])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['3', '4'])).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.04           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 0.83/1.04           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['6', '7'])).
% 0.83/1.04  thf(t46_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      (![X8 : $i, X9 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.83/1.04      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.83/1.04  thf('10', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1) = (k1_xboole_0))),
% 0.83/1.04      inference('demod', [status(thm)], ['8', '9'])).
% 0.83/1.04  thf('11', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['10', '11'])).
% 0.83/1.04  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.04      inference('demod', [status(thm)], ['5', '12'])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.83/1.04           = (k1_xboole_0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['2', '13'])).
% 0.83/1.04  thf(t39_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (![X2 : $i, X3 : $i]:
% 0.83/1.04         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.04           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.83/1.04      inference('demod', [status(thm)], ['14', '15'])).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.04         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.04           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      (![X2 : $i, X3 : $i]:
% 0.83/1.04         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.04           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.83/1.04           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['17', '18'])).
% 0.83/1.05  thf('20', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.83/1.05           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['16', '19'])).
% 0.83/1.05  thf(t92_xboole_1, axiom,
% 0.83/1.05    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.83/1.05  thf('21', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.05  thf(t91_xboole_1, axiom,
% 0.83/1.05    (![A:$i,B:$i,C:$i]:
% 0.83/1.05     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.83/1.05       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.83/1.05  thf('22', plain,
% 0.83/1.05      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.05           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.05  thf('23', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.83/1.05           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['21', '22'])).
% 0.83/1.05  thf(commutativity_k5_xboole_0, axiom,
% 0.83/1.05    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.83/1.05  thf('24', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.05  thf(t5_boole, axiom,
% 0.83/1.05    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.05  thf('25', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.83/1.05      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.05  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['24', '25'])).
% 0.83/1.05  thf('27', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['23', '26'])).
% 0.83/1.05  thf(t94_xboole_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( k2_xboole_0 @ A @ B ) =
% 0.83/1.05       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.83/1.05  thf('28', plain,
% 0.83/1.05      (![X17 : $i, X18 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X17 @ X18)
% 0.83/1.05           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.83/1.05              (k3_xboole_0 @ X17 @ X18)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.83/1.05  thf('29', plain,
% 0.83/1.05      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.83/1.05           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.05  thf('30', plain,
% 0.83/1.05      (![X17 : $i, X18 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X17 @ X18)
% 0.83/1.05           = (k5_xboole_0 @ X17 @ 
% 0.83/1.05              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.83/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.05  thf('31', plain,
% 0.83/1.05      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['27', '30'])).
% 0.83/1.05  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['5', '12'])).
% 0.83/1.05  thf('33', plain,
% 0.83/1.05      (![X10 : $i, X11 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.05           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.05  thf('34', plain,
% 0.83/1.05      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['32', '33'])).
% 0.83/1.05  thf('35', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.83/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.05  thf('36', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['34', '35'])).
% 0.83/1.05  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['31', '36'])).
% 0.83/1.05  thf('38', plain,
% 0.83/1.05      (![X8 : $i, X9 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.83/1.05  thf('39', plain,
% 0.83/1.05      (![X2 : $i, X3 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.05           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.05  thf('40', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.83/1.05           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['38', '39'])).
% 0.83/1.05  thf('41', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.83/1.05           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['37', '40'])).
% 0.83/1.05  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['31', '36'])).
% 0.83/1.05  thf('43', plain,
% 0.83/1.05      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['41', '42'])).
% 0.83/1.05  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['31', '36'])).
% 0.83/1.05  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('46', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['20', '45'])).
% 0.83/1.05  thf('47', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X1) = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['1', '46'])).
% 0.83/1.05  thf('48', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.05           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.05  thf('49', plain,
% 0.83/1.05      (![X10 : $i, X11 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.05           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.05  thf('50', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X2 @ 
% 0.83/1.05           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.83/1.05           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['48', '49'])).
% 0.83/1.05  thf('51', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.05           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.05  thf('52', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X2 @ 
% 0.83/1.05           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.83/1.05           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['50', '51'])).
% 0.83/1.05  thf('53', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)))
% 0.83/1.05           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['47', '52'])).
% 0.83/1.05  thf('54', plain,
% 0.83/1.05      (![X2 : $i, X3 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.05           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.05  thf('55', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['14', '15'])).
% 0.83/1.05  thf('56', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k1_xboole_0)
% 0.83/1.05           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.83/1.05      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.83/1.05  thf('57', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['14', '15'])).
% 0.83/1.05  thf('58', plain,
% 0.83/1.05      (![X10 : $i, X11 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.05           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.05  thf('59', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.83/1.05           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['57', '58'])).
% 0.83/1.05  thf('60', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.83/1.05      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.05  thf('61', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['59', '60'])).
% 0.83/1.05  thf('62', plain,
% 0.83/1.05      (![X17 : $i, X18 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X17 @ X18)
% 0.83/1.05           = (k5_xboole_0 @ X17 @ 
% 0.83/1.05              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.83/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.05  thf('63', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['61', '62'])).
% 0.83/1.05  thf('64', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.05  thf('65', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['23', '26'])).
% 0.83/1.05  thf('66', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.83/1.05  thf('67', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.05           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.05  thf('68', plain,
% 0.83/1.05      (![X8 : $i, X9 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.83/1.05  thf('69', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X2 @ 
% 0.83/1.05           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.83/1.05           = (k1_xboole_0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['67', '68'])).
% 0.83/1.05  thf('70', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 0.83/1.05           = (k1_xboole_0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['66', '69'])).
% 0.83/1.05  thf('71', plain,
% 0.83/1.05      (![X10 : $i, X11 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.83/1.05           = (k3_xboole_0 @ X10 @ X11))),
% 0.83/1.05      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.05  thf('72', plain,
% 0.83/1.05      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.83/1.05           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.83/1.05  thf('73', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.05           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['71', '72'])).
% 0.83/1.05  thf('74', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['70', '73'])).
% 0.83/1.05  thf('75', plain,
% 0.83/1.05      (![X2 : $i, X3 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.05           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.05  thf('76', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.83/1.05           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['74', '75'])).
% 0.83/1.05  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('78', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['76', '77'])).
% 0.83/1.05  thf('79', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.83/1.05  thf('80', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.83/1.05           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['78', '79'])).
% 0.83/1.05  thf('81', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['76', '77'])).
% 0.83/1.05  thf('82', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['80', '81'])).
% 0.83/1.05  thf('83', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.83/1.05           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['38', '39'])).
% 0.83/1.05  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['43', '44'])).
% 0.83/1.05  thf('85', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ X1)
% 0.83/1.05           = (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['83', '84'])).
% 0.83/1.05  thf('86', plain,
% 0.83/1.05      (![X17 : $i, X18 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X17 @ X18)
% 0.83/1.05           = (k5_xboole_0 @ X17 @ 
% 0.83/1.05              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.83/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.05  thf('87', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['23', '26'])).
% 0.83/1.05  thf('88', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['86', '87'])).
% 0.83/1.05  thf('89', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 0.83/1.05           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['85', '88'])).
% 0.83/1.05  thf('90', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.05  thf('91', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 0.83/1.05           = (k1_xboole_0))),
% 0.83/1.05      inference('demod', [status(thm)], ['89', '90'])).
% 0.83/1.05  thf('92', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['23', '26'])).
% 0.83/1.05  thf('93', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.83/1.05           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['91', '92'])).
% 0.83/1.05  thf('94', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.83/1.05      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.05  thf('95', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['93', '94'])).
% 0.83/1.05  thf('96', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k3_xboole_0 @ X1 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['82', '95'])).
% 0.83/1.05  thf('97', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['56', '96'])).
% 0.83/1.05  thf('98', plain,
% 0.83/1.05      (![X17 : $i, X18 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X17 @ X18)
% 0.83/1.05           = (k5_xboole_0 @ X17 @ 
% 0.83/1.05              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.83/1.05      inference('demod', [status(thm)], ['28', '29'])).
% 0.83/1.05  thf('99', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.83/1.05           = (k5_xboole_0 @ X0 @ 
% 0.83/1.05              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['97', '98'])).
% 0.83/1.05  thf('100', plain,
% 0.83/1.05      (![X2 : $i, X3 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.83/1.05           = (k2_xboole_0 @ X2 @ X3))),
% 0.83/1.05      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.83/1.05  thf('101', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.05  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['24', '25'])).
% 0.83/1.05  thf('103', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k2_xboole_0 @ X0 @ X1)
% 0.83/1.05           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['99', '100', '101', '102'])).
% 0.83/1.05  thf('104', plain,
% 0.83/1.05      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.05      inference('demod', [status(thm)], ['0', '103'])).
% 0.83/1.05  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 0.83/1.05  
% 0.83/1.05  % SZS output end Refutation
% 0.83/1.05  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
