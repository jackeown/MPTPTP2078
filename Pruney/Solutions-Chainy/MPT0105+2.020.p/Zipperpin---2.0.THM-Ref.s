%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nR0zgUy04e

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:07 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 214 expanded)
%              Number of leaves         :   18 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  682 (1755 expanded)
%              Number of equality atoms :   77 ( 206 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X3 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','22','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','53','54','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nR0zgUy04e
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:03:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 940 iterations in 0.426s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(t98_xboole_1, conjecture,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i,B:$i]:
% 0.70/0.88        ( ( k2_xboole_0 @ A @ B ) =
% 0.70/0.88          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.70/0.88  thf('0', plain,
% 0.70/0.88      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.70/0.88         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t41_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.88       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.70/0.88  thf('1', plain,
% 0.70/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.70/0.88           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.88  thf('2', plain,
% 0.70/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.70/0.88           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.88  thf(t3_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.88  thf('3', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.70/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.70/0.88  thf('4', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 0.70/0.88           = (k4_xboole_0 @ X1 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['2', '3'])).
% 0.70/0.88  thf(t46_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('5', plain,
% 0.70/0.88      (![X8 : $i, X9 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.70/0.88  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['1', '6'])).
% 0.70/0.88  thf(t39_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('8', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('9', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.88  thf(t49_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.70/0.88       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.88  thf('11', plain,
% 0.70/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.70/0.88           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.88  thf('12', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['11', '12'])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ 
% 0.70/0.88           (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.70/0.88           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k3_xboole_0 @ X3 @ X2) @ X1)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['10', '13'])).
% 0.70/0.88  thf('15', plain,
% 0.70/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.88  thf('16', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ 
% 0.70/0.88           (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.70/0.88           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ X1))))),
% 0.70/0.88      inference('demod', [status(thm)], ['14', '15'])).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ k1_xboole_0))
% 0.70/0.88           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.70/0.88      inference('sup+', [status(thm)], ['9', '16'])).
% 0.70/0.88  thf(t4_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.88  thf('18', plain,
% 0.70/0.88      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.70/0.88      inference('cnf', [status(esa)], [t4_boole])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.88  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['19', '20'])).
% 0.70/0.88  thf('22', plain,
% 0.70/0.88      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['18', '21'])).
% 0.70/0.88  thf(t5_boole, axiom,
% 0.70/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.88  thf('23', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf(t91_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.70/0.88       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.70/0.88           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ X0 @ X1)
% 0.70/0.88           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['23', '24'])).
% 0.70/0.88  thf(t94_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k2_xboole_0 @ A @ B ) =
% 0.70/0.88       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.88           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.70/0.88              (k3_xboole_0 @ X18 @ X19)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.70/0.88  thf('27', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.70/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.70/0.88           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.88           = (k5_xboole_0 @ X18 @ 
% 0.70/0.88              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 0.70/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.70/0.88           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['25', '28'])).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['18', '21'])).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['29', '30'])).
% 0.70/0.88  thf('32', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((X1)
% 0.70/0.88           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.70/0.88      inference('demod', [status(thm)], ['17', '22', '33'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.88  thf('36', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('37', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['35', '36'])).
% 0.70/0.88  thf('38', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['34', '37'])).
% 0.70/0.88  thf('39', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('40', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('41', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['7', '8'])).
% 0.70/0.88  thf('42', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['40', '41'])).
% 0.70/0.88  thf('43', plain,
% 0.70/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.70/0.88           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.88  thf('44', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['42', '43'])).
% 0.70/0.88  thf('45', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.70/0.88           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['39', '44'])).
% 0.70/0.88  thf('46', plain,
% 0.70/0.88      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.70/0.88           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.70/0.88  thf('47', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X0 @ 
% 0.70/0.88           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))
% 0.70/0.88           = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['45', '46'])).
% 0.70/0.88  thf('48', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.70/0.88           (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['38', '47'])).
% 0.70/0.88  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.70/0.88  thf('50', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('51', plain,
% 0.70/0.88      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['49', '50'])).
% 0.70/0.88  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.70/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.70/0.88  thf('53', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.70/0.88  thf('54', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.70/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.70/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.70/0.88  thf('55', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.70/0.88  thf('56', plain,
% 0.70/0.88      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.70/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.70/0.88  thf('57', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.70/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.70/0.88      inference('sup+', [status(thm)], ['55', '56'])).
% 0.70/0.88  thf('58', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.70/0.88      inference('demod', [status(thm)], ['48', '53', '54', '57'])).
% 0.70/0.88  thf('59', plain,
% 0.70/0.88      (![X18 : $i, X19 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X18 @ X19)
% 0.70/0.88           = (k5_xboole_0 @ X18 @ 
% 0.70/0.88              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 0.70/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.70/0.88  thf('60', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.70/0.88           = (k5_xboole_0 @ X0 @ 
% 0.70/0.88              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['58', '59'])).
% 0.70/0.88  thf('61', plain,
% 0.70/0.88      (![X2 : $i, X3 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 0.70/0.88           = (k2_xboole_0 @ X2 @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.70/0.88  thf('62', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.70/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.88  thf('63', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k2_xboole_0 @ X0 @ X1)
% 0.70/0.88           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.70/0.88      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.70/0.88  thf('64', plain,
% 0.70/0.88      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.70/0.88      inference('demod', [status(thm)], ['0', '63'])).
% 0.70/0.88  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.70/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
