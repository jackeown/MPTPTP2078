%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n640OlxUGB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:00 EST 2020

% Result     : Theorem 51.08s
% Output     : Refutation 51.08s
% Verified   : 
% Statistics : Number of formulae       :  219 (2276 expanded)
%              Number of leaves         :   18 ( 811 expanded)
%              Depth                    :   23
%              Number of atoms          : 1968 (17839 expanded)
%              Number of equality atoms :  211 (2268 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['51','52','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','65'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['71','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['66','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','82','83'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('97',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','82','83'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','109'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','110','111','112'])).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('116',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','65'])).

thf('120',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','113','114','115','116','117','118','119','120','121'])).

thf('123',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('124',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('134',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('135',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['133','138'])).

thf('140',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('142',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('146',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('147',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('151',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['144','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('158',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('159',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','39'])).

thf('163',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','164'])).

thf('166',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['156','168'])).

thf('170',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','109'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('175',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['173','182'])).

thf('184',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('188',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','34'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['189','190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','172','185','186','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['132','195'])).

thf('197',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('198',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','196','197'])).

thf('199',plain,(
    $false ),
    inference(simplify,[status(thm)],['198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.n640OlxUGB
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:38:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 51.08/51.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 51.08/51.41  % Solved by: fo/fo7.sh
% 51.08/51.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.08/51.41  % done 13713 iterations in 50.958s
% 51.08/51.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 51.08/51.41  % SZS output start Refutation
% 51.08/51.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 51.08/51.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.08/51.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 51.08/51.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.08/51.41  thf(sk_B_type, type, sk_B: $i).
% 51.08/51.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.08/51.41  thf(sk_A_type, type, sk_A: $i).
% 51.08/51.41  thf(t95_xboole_1, conjecture,
% 51.08/51.41    (![A:$i,B:$i]:
% 51.08/51.41     ( ( k3_xboole_0 @ A @ B ) =
% 51.08/51.41       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 51.08/51.41  thf(zf_stmt_0, negated_conjecture,
% 51.08/51.41    (~( ![A:$i,B:$i]:
% 51.08/51.41        ( ( k3_xboole_0 @ A @ B ) =
% 51.08/51.41          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 51.08/51.41    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 51.08/51.41  thf('0', plain,
% 51.08/51.41      (((k3_xboole_0 @ sk_A @ sk_B)
% 51.08/51.41         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 51.08/51.41             (k2_xboole_0 @ sk_A @ sk_B)))),
% 51.08/51.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.08/51.41  thf(d6_xboole_0, axiom,
% 51.08/51.41    (![A:$i,B:$i]:
% 51.08/51.41     ( ( k5_xboole_0 @ A @ B ) =
% 51.08/51.41       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 51.08/51.41  thf('1', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf(commutativity_k2_xboole_0, axiom,
% 51.08/51.41    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 51.08/51.41  thf('2', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('3', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['1', '2'])).
% 51.08/51.41  thf('4', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('5', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['3', '4'])).
% 51.08/51.41  thf(t41_xboole_1, axiom,
% 51.08/51.41    (![A:$i,B:$i,C:$i]:
% 51.08/51.41     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 51.08/51.41       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 51.08/51.41  thf('6', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('7', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('8', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 51.08/51.41           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['6', '7'])).
% 51.08/51.41  thf('9', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('10', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('11', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 51.08/51.41           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 51.08/51.41      inference('demod', [status(thm)], ['8', '9', '10'])).
% 51.08/51.41  thf('12', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf(t3_boole, axiom,
% 51.08/51.41    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 51.08/51.41  thf('13', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 51.08/51.41      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.41  thf(t48_xboole_1, axiom,
% 51.08/51.41    (![A:$i,B:$i]:
% 51.08/51.41     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 51.08/51.41  thf('14', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('15', plain,
% 51.08/51.41      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['13', '14'])).
% 51.08/51.41  thf('16', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('17', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 51.08/51.41      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.41  thf('18', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('19', plain,
% 51.08/51.41      (![X0 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 51.08/51.41           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['17', '18'])).
% 51.08/51.41  thf(t5_boole, axiom,
% 51.08/51.41    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 51.08/51.41  thf('20', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 51.08/51.41      inference('cnf', [status(esa)], [t5_boole])).
% 51.08/51.41  thf('21', plain,
% 51.08/51.41      (![X0 : $i]:
% 51.08/51.41         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['19', '20'])).
% 51.08/51.41  thf('22', plain,
% 51.08/51.41      (![X0 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 51.08/51.41              (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['16', '21'])).
% 51.08/51.41  thf('23', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf(t51_xboole_1, axiom,
% 51.08/51.41    (![A:$i,B:$i]:
% 51.08/51.41     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 51.08/51.41       ( A ) ))).
% 51.08/51.41  thf('24', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('25', plain,
% 51.08/51.41      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['22', '23', '24'])).
% 51.08/51.41  thf(commutativity_k3_xboole_0, axiom,
% 51.08/51.41    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 51.08/51.41  thf('26', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('27', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('28', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 51.08/51.41           = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['26', '27'])).
% 51.08/51.41  thf('29', plain,
% 51.08/51.41      (![X0 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 51.08/51.41           = (k1_xboole_0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['25', '28'])).
% 51.08/51.41  thf('30', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('31', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf(t1_boole, axiom,
% 51.08/51.41    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 51.08/51.41  thf('32', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['31', '32'])).
% 51.08/51.41  thf('34', plain,
% 51.08/51.41      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['29', '30', '33'])).
% 51.08/51.41  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['15', '34'])).
% 51.08/51.41  thf('36', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('37', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['35', '36'])).
% 51.08/51.41  thf('38', plain,
% 51.08/51.41      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['22', '23', '24'])).
% 51.08/51.41  thf('39', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['37', '38'])).
% 51.08/51.41  thf('40', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['12', '39'])).
% 51.08/51.41  thf('41', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k1_xboole_0)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['11', '40'])).
% 51.08/51.41  thf('42', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['1', '2'])).
% 51.08/51.41  thf(t40_xboole_1, axiom,
% 51.08/51.41    (![A:$i,B:$i]:
% 51.08/51.41     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 51.08/51.41  thf('43', plain,
% 51.08/51.41      (![X8 : $i, X9 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 51.08/51.41           = (k4_xboole_0 @ X8 @ X9))),
% 51.08/51.41      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.08/51.41  thf('44', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('45', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 51.08/51.41           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['43', '44'])).
% 51.08/51.41  thf('46', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('47', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 51.08/51.41           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 51.08/51.41      inference('demod', [status(thm)], ['45', '46'])).
% 51.08/51.41  thf('48', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 51.08/51.41           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['42', '47'])).
% 51.08/51.41  thf('49', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('50', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ 
% 51.08/51.41           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 51.08/51.41      inference('demod', [status(thm)], ['48', '49'])).
% 51.08/51.41  thf('51', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0)
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['41', '50'])).
% 51.08/51.41  thf('52', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('53', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('54', plain,
% 51.08/51.41      (![X8 : $i, X9 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 51.08/51.41           = (k4_xboole_0 @ X8 @ X9))),
% 51.08/51.41      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.08/51.41  thf('55', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['53', '54'])).
% 51.08/51.41  thf('56', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('57', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 51.08/51.41           (k4_xboole_0 @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['55', '56'])).
% 51.08/51.41  thf('58', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('59', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['37', '38'])).
% 51.08/51.41  thf('60', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('61', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 51.08/51.41           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['59', '60'])).
% 51.08/51.41  thf('62', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 51.08/51.41      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.41  thf('63', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['61', '62'])).
% 51.08/51.41  thf('64', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('demod', [status(thm)], ['57', '58', '63'])).
% 51.08/51.41  thf('65', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0)
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['51', '52', '64'])).
% 51.08/51.41  thf('66', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0)
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['5', '65'])).
% 51.08/51.41  thf('67', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('68', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('69', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X2 @ 
% 51.08/51.41              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['67', '68'])).
% 51.08/51.41  thf('70', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('71', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X2 @ 
% 51.08/51.41              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 51.08/51.41      inference('demod', [status(thm)], ['69', '70'])).
% 51.08/51.41  thf('72', plain,
% 51.08/51.41      (![X8 : $i, X9 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 51.08/51.41           = (k4_xboole_0 @ X8 @ X9))),
% 51.08/51.41      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.08/51.41  thf('73', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('74', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 51.08/51.41           (k4_xboole_0 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['72', '73'])).
% 51.08/51.41  thf('75', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('76', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('77', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 51.08/51.41           = (k2_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['74', '75', '76'])).
% 51.08/51.41  thf('78', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['12', '39'])).
% 51.08/51.41  thf('79', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('80', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 51.08/51.41           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['78', '79'])).
% 51.08/51.41  thf('81', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 51.08/51.41      inference('cnf', [status(esa)], [t3_boole])).
% 51.08/51.41  thf('82', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['80', '81'])).
% 51.08/51.41  thf('83', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('84', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['77', '82', '83'])).
% 51.08/51.41  thf('85', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ 
% 51.08/51.41           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 51.08/51.41           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X2 @ 
% 51.08/51.41              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['71', '84'])).
% 51.08/51.41  thf('86', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('87', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 51.08/51.41           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 51.08/51.41           = (k2_xboole_0 @ X2 @ 
% 51.08/51.41              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 51.08/51.41      inference('demod', [status(thm)], ['85', '86'])).
% 51.08/51.41  thf('88', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ 
% 51.08/51.41           (k3_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1) @ X0) @ 
% 51.08/51.41           (k2_xboole_0 @ X1 @ k1_xboole_0))
% 51.08/51.41           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k2_xboole_0 @ X1 @ 
% 51.08/51.41               (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['66', '87'])).
% 51.08/51.41  thf('89', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['12', '39'])).
% 51.08/51.41  thf('90', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['77', '82', '83'])).
% 51.08/51.41  thf('91', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 51.08/51.41           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['89', '90'])).
% 51.08/51.41  thf('92', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('93', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X1 @ X0)
% 51.08/51.41           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['91', '92'])).
% 51.08/51.41  thf('94', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ 
% 51.08/51.41           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 51.08/51.41      inference('demod', [status(thm)], ['48', '49'])).
% 51.08/51.41  thf('95', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ 
% 51.08/51.41              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['93', '94'])).
% 51.08/51.41  thf('96', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('97', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('98', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['80', '81'])).
% 51.08/51.41  thf('99', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ X1)
% 51.08/51.41           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['97', '98'])).
% 51.08/51.41  thf('100', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('101', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ X1)
% 51.08/51.41           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['99', '100'])).
% 51.08/51.41  thf('102', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('103', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['37', '38'])).
% 51.08/51.41  thf('104', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['102', '103'])).
% 51.08/51.41  thf('105', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['77', '82', '83'])).
% 51.08/51.41  thf('106', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 51.08/51.41           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['104', '105'])).
% 51.08/51.41  thf('107', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('108', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('109', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['106', '107', '108'])).
% 51.08/51.41  thf('110', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['101', '109'])).
% 51.08/51.41  thf('111', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('112', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['101', '109'])).
% 51.08/51.41  thf('113', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X1 @ X0)
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['95', '96', '110', '111', '112'])).
% 51.08/51.41  thf('114', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('115', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ X1)
% 51.08/51.41           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['99', '100'])).
% 51.08/51.41  thf('116', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('117', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('118', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('demod', [status(thm)], ['57', '58', '63'])).
% 51.08/51.41  thf('119', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0)
% 51.08/51.41           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['5', '65'])).
% 51.08/51.41  thf('120', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('121', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('122', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ X1 @ X0)
% 51.08/51.41           = (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)],
% 51.08/51.41                ['88', '113', '114', '115', '116', '117', '118', '119', '120', 
% 51.08/51.41                 '121'])).
% 51.08/51.41  thf('123', plain,
% 51.08/51.41      (![X8 : $i, X9 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 51.08/51.41           = (k4_xboole_0 @ X8 @ X9))),
% 51.08/51.41      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.08/51.41  thf('124', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('125', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 51.08/51.41              (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['123', '124'])).
% 51.08/51.41  thf('126', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('127', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 51.08/51.41      inference('demod', [status(thm)], ['125', '126'])).
% 51.08/51.41  thf('128', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['12', '39'])).
% 51.08/51.41  thf('129', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('130', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['31', '32'])).
% 51.08/51.41  thf('131', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k4_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 51.08/51.41  thf('132', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['122', '131'])).
% 51.08/51.41  thf('133', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['53', '54'])).
% 51.08/51.41  thf('134', plain,
% 51.08/51.41      (![X15 : $i, X16 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ (k4_xboole_0 @ X15 @ X16))
% 51.08/51.41           = (X15))),
% 51.08/51.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 51.08/51.41  thf('135', plain,
% 51.08/51.41      (![X8 : $i, X9 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 51.08/51.41           = (k4_xboole_0 @ X8 @ X9))),
% 51.08/51.41      inference('cnf', [status(esa)], [t40_xboole_1])).
% 51.08/51.41  thf('136', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.08/51.41           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['134', '135'])).
% 51.08/51.41  thf('137', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('138', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k3_xboole_0 @ X0 @ X1)
% 51.08/51.41           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['136', '137'])).
% 51.08/51.41  thf('139', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 51.08/51.41           = (k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 51.08/51.41              (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['133', '138'])).
% 51.08/51.41  thf('140', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('141', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['61', '62'])).
% 51.08/51.41  thf('142', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('143', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['61', '62'])).
% 51.08/51.41  thf('144', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 51.08/51.41  thf('145', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['1', '2'])).
% 51.08/51.41  thf('146', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('147', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('148', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 51.08/51.41              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['146', '147'])).
% 51.08/51.41  thf('149', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 51.08/51.41           (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 51.08/51.41              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['145', '148'])).
% 51.08/51.41  thf('150', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['3', '4'])).
% 51.08/51.41  thf('151', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('152', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 51.08/51.41              (k4_xboole_0 @ X1 @ 
% 51.08/51.41               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))))),
% 51.08/51.41      inference('demod', [status(thm)], ['149', '150', '151'])).
% 51.08/51.41  thf('153', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 51.08/51.41           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)) @ 
% 51.08/51.41              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['144', '152'])).
% 51.08/51.41  thf('154', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['139', '140', '141', '142', '143'])).
% 51.08/51.41  thf('155', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['3', '4'])).
% 51.08/51.41  thf('156', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 51.08/51.41           = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['26', '27'])).
% 51.08/51.41  thf('157', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['53', '54'])).
% 51.08/51.41  thf('158', plain,
% 51.08/51.41      (![X13 : $i, X14 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 51.08/51.41           = (k3_xboole_0 @ X13 @ X14))),
% 51.08/51.41      inference('cnf', [status(esa)], [t48_xboole_1])).
% 51.08/51.41  thf('159', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('160', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['158', '159'])).
% 51.08/51.41  thf('161', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('162', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['12', '39'])).
% 51.08/51.41  thf('163', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 51.08/51.41      inference('cnf', [status(esa)], [t1_boole])).
% 51.08/51.41  thf('164', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k3_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 51.08/51.41  thf('165', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['157', '164'])).
% 51.08/51.41  thf('166', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('167', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['61', '62'])).
% 51.08/51.41  thf('168', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['165', '166', '167'])).
% 51.08/51.41  thf('169', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ 
% 51.08/51.41           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 51.08/51.41           = (k3_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['156', '168'])).
% 51.08/51.41  thf('170', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('171', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)], ['106', '107', '108'])).
% 51.08/51.41  thf('172', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.08/51.41           = (k3_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['169', '170', '171'])).
% 51.08/51.41  thf('173', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['101', '109'])).
% 51.08/51.41  thf('174', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['53', '54'])).
% 51.08/51.41  thf('175', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('176', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.08/51.41              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 51.08/51.41      inference('sup+', [status(thm)], ['174', '175'])).
% 51.08/51.41  thf('177', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['37', '38'])).
% 51.08/51.41  thf('178', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('179', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['31', '32'])).
% 51.08/51.41  thf('180', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 51.08/51.41  thf('181', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['3', '4'])).
% 51.08/51.41  thf('182', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 51.08/51.41           = (k4_xboole_0 @ X1 @ X0))),
% 51.08/51.41      inference('demod', [status(thm)], ['180', '181'])).
% 51.08/51.41  thf('183', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ X0)
% 51.08/51.41           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['173', '182'])).
% 51.08/51.41  thf('184', plain,
% 51.08/51.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 51.08/51.41         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 51.08/51.41           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 51.08/51.41      inference('cnf', [status(esa)], [t41_xboole_1])).
% 51.08/51.41  thf('185', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 51.08/51.41      inference('demod', [status(thm)], ['183', '184'])).
% 51.08/51.41  thf('186', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 51.08/51.41  thf('187', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['15', '34'])).
% 51.08/51.41  thf('188', plain,
% 51.08/51.41      (![X4 : $i, X5 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X4 @ X5)
% 51.08/51.41           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 51.08/51.41      inference('cnf', [status(esa)], [d6_xboole_0])).
% 51.08/51.41  thf('189', plain,
% 51.08/51.41      (![X0 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ X0 @ X0)
% 51.08/51.41           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 51.08/51.41      inference('sup+', [status(thm)], ['187', '188'])).
% 51.08/51.41  thf('190', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['15', '34'])).
% 51.08/51.41  thf('191', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['31', '32'])).
% 51.08/51.41  thf('192', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 51.08/51.41      inference('demod', [status(thm)], ['189', '190', '191'])).
% 51.08/51.41  thf('193', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 51.08/51.41      inference('sup+', [status(thm)], ['31', '32'])).
% 51.08/51.41  thf('194', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 51.08/51.41      inference('sup+', [status(thm)], ['192', '193'])).
% 51.08/51.41  thf('195', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k3_xboole_0 @ X1 @ X0)
% 51.08/51.41           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 51.08/51.41      inference('demod', [status(thm)],
% 51.08/51.41                ['153', '154', '155', '172', '185', '186', '194'])).
% 51.08/51.41  thf('196', plain,
% 51.08/51.41      (![X0 : $i, X1 : $i]:
% 51.08/51.41         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 51.08/51.41           = (k3_xboole_0 @ X0 @ X1))),
% 51.08/51.41      inference('demod', [status(thm)], ['132', '195'])).
% 51.08/51.41  thf('197', plain,
% 51.08/51.41      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 51.08/51.41      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 51.08/51.41  thf('198', plain,
% 51.08/51.41      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 51.08/51.41      inference('demod', [status(thm)], ['0', '196', '197'])).
% 51.08/51.41  thf('199', plain, ($false), inference('simplify', [status(thm)], ['198'])).
% 51.08/51.41  
% 51.08/51.41  % SZS output end Refutation
% 51.08/51.41  
% 51.20/51.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
