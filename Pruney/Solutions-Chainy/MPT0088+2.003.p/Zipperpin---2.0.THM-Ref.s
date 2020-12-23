%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6IoeMZlenK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 177 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  697 (1406 expanded)
%              Number of equality atoms :   73 ( 158 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['39','40','41','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_C ) ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['6','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['5','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('64',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59','62','63'])).

thf('65',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6IoeMZlenK
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.44  % Solved by: fo/fo7.sh
% 1.18/1.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.44  % done 893 iterations in 0.930s
% 1.18/1.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.44  % SZS output start Refutation
% 1.18/1.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.18/1.44  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.18/1.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.44  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.44  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.18/1.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.18/1.44  thf(t81_xboole_1, conjecture,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.18/1.44       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.18/1.44  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.44    (~( ![A:$i,B:$i,C:$i]:
% 1.18/1.44        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.18/1.44          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 1.18/1.44    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 1.18/1.44  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(t48_xboole_1, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.18/1.44  thf('1', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf(t41_xboole_1, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.18/1.44       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.18/1.44  thf('2', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('3', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.18/1.44           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['1', '2'])).
% 1.18/1.44  thf(t49_xboole_1, axiom,
% 1.18/1.44    (![A:$i,B:$i,C:$i]:
% 1.18/1.44     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.18/1.44       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.18/1.44  thf('4', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('5', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X2))
% 1.18/1.44           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.18/1.44      inference('demod', [status(thm)], ['3', '4'])).
% 1.18/1.44  thf(commutativity_k2_xboole_0, axiom,
% 1.18/1.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.18/1.44  thf('6', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.18/1.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.18/1.44  thf(t3_boole, axiom,
% 1.18/1.44    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.18/1.44  thf('7', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.18/1.44      inference('cnf', [status(esa)], [t3_boole])).
% 1.18/1.44  thf('8', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf('9', plain,
% 1.18/1.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.18/1.44      inference('sup+', [status(thm)], ['7', '8'])).
% 1.18/1.44  thf(t2_boole, axiom,
% 1.18/1.44    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.18/1.44  thf('10', plain,
% 1.18/1.44      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 1.18/1.44      inference('cnf', [status(esa)], [t2_boole])).
% 1.18/1.44  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.18/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.18/1.44  thf('12', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('13', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k1_xboole_0)
% 1.18/1.44           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.18/1.44      inference('sup+', [status(thm)], ['11', '12'])).
% 1.18/1.44  thf(t39_xboole_1, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.18/1.44  thf('14', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.18/1.44           = (k2_xboole_0 @ X8 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.18/1.44  thf('15', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.18/1.44      inference('demod', [status(thm)], ['13', '14'])).
% 1.18/1.44  thf('16', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('17', plain,
% 1.18/1.44      (![X8 : $i, X9 : $i]:
% 1.18/1.44         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.18/1.44           = (k2_xboole_0 @ X8 @ X9))),
% 1.18/1.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.18/1.44  thf('18', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.18/1.44           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['16', '17'])).
% 1.18/1.44  thf('19', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.18/1.44           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['15', '18'])).
% 1.18/1.44  thf('20', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.18/1.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.44  thf(d7_xboole_0, axiom,
% 1.18/1.44    (![A:$i,B:$i]:
% 1.18/1.44     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.18/1.44       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.18/1.44  thf('21', plain,
% 1.18/1.44      (![X2 : $i, X3 : $i]:
% 1.18/1.44         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.18/1.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.18/1.44  thf('22', plain,
% 1.18/1.44      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.18/1.44      inference('sup-', [status(thm)], ['20', '21'])).
% 1.18/1.44  thf('23', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf('24', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf('25', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.44           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['23', '24'])).
% 1.18/1.44  thf('26', plain,
% 1.18/1.44      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 1.18/1.44         = (k3_xboole_0 @ sk_A @ 
% 1.18/1.44            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 1.18/1.44      inference('sup+', [status(thm)], ['22', '25'])).
% 1.18/1.44  thf('27', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.18/1.44      inference('cnf', [status(esa)], [t3_boole])).
% 1.18/1.44  thf('28', plain,
% 1.18/1.44      (((sk_A)
% 1.18/1.44         = (k3_xboole_0 @ sk_A @ 
% 1.18/1.44            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 1.18/1.44      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.44  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.18/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.18/1.44  thf('30', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf('31', plain,
% 1.18/1.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.18/1.44      inference('sup+', [status(thm)], ['29', '30'])).
% 1.18/1.44  thf('32', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.18/1.44      inference('cnf', [status(esa)], [t3_boole])).
% 1.18/1.44  thf('33', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.18/1.44      inference('demod', [status(thm)], ['31', '32'])).
% 1.18/1.44  thf('34', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('35', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.18/1.44           = (k4_xboole_0 @ X0 @ X1))),
% 1.18/1.44      inference('sup+', [status(thm)], ['33', '34'])).
% 1.18/1.44  thf('36', plain,
% 1.18/1.44      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.18/1.44      inference('demod', [status(thm)], ['28', '35'])).
% 1.18/1.44  thf('37', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('38', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ sk_A @ X0)
% 1.18/1.44           = (k4_xboole_0 @ sk_A @ 
% 1.18/1.44              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['36', '37'])).
% 1.18/1.44  thf('39', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ sk_A @ 
% 1.18/1.44           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0))
% 1.18/1.44           = (k4_xboole_0 @ sk_A @ 
% 1.18/1.44              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ k1_xboole_0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['19', '38'])).
% 1.18/1.44  thf('40', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('41', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.18/1.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.18/1.44  thf('42', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.18/1.44      inference('cnf', [status(esa)], [t3_boole])).
% 1.18/1.44  thf('43', plain,
% 1.18/1.44      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.18/1.44           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.18/1.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.18/1.44  thf('44', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X0 @ X1)
% 1.18/1.44           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['42', '43'])).
% 1.18/1.44  thf('45', plain,
% 1.18/1.44      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.18/1.44      inference('demod', [status(thm)], ['28', '35'])).
% 1.18/1.44  thf('46', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ sk_A @ 
% 1.18/1.44           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))) = (sk_A))),
% 1.18/1.44      inference('demod', [status(thm)], ['39', '40', '41', '44', '45'])).
% 1.18/1.44  thf('47', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ sk_A @ 
% 1.18/1.44           (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_C))) = (sk_A))),
% 1.18/1.44      inference('sup+', [status(thm)], ['6', '46'])).
% 1.18/1.44  thf('48', plain,
% 1.18/1.44      (![X0 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ sk_A @ 
% 1.18/1.44           (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))) = (sk_A))),
% 1.18/1.44      inference('sup+', [status(thm)], ['5', '47'])).
% 1.18/1.44  thf('49', plain,
% 1.18/1.44      (![X14 : $i, X15 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.18/1.44           = (k3_xboole_0 @ X14 @ X15))),
% 1.18/1.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.18/1.44  thf('50', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('51', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X2 @ 
% 1.18/1.44           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 1.18/1.44           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.18/1.44      inference('sup+', [status(thm)], ['49', '50'])).
% 1.18/1.44  thf('52', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('53', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X2 @ 
% 1.18/1.44           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 1.18/1.44           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 1.18/1.44      inference('demod', [status(thm)], ['51', '52'])).
% 1.18/1.44  thf('54', plain,
% 1.18/1.44      (((k3_xboole_0 @ sk_B @ sk_A)
% 1.18/1.44         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.18/1.44      inference('sup+', [status(thm)], ['48', '53'])).
% 1.18/1.44  thf('55', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.44           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.18/1.44      inference('sup+', [status(thm)], ['23', '24'])).
% 1.18/1.44  thf('56', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.18/1.44           = (k4_xboole_0 @ X0 @ X1))),
% 1.18/1.44      inference('sup+', [status(thm)], ['33', '34'])).
% 1.18/1.44  thf('57', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.18/1.44           = (k4_xboole_0 @ X1 @ X0))),
% 1.18/1.44      inference('demod', [status(thm)], ['55', '56'])).
% 1.18/1.44  thf('58', plain,
% 1.18/1.44      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.18/1.44         (k3_xboole_0 @ sk_B @ sk_A))
% 1.18/1.44         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 1.18/1.44      inference('sup+', [status(thm)], ['54', '57'])).
% 1.18/1.44  thf('59', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('60', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.18/1.44      inference('demod', [status(thm)], ['9', '10'])).
% 1.18/1.44  thf('62', plain,
% 1.18/1.44      (![X0 : $i, X1 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.18/1.44           = (k1_xboole_0))),
% 1.18/1.44      inference('sup+', [status(thm)], ['60', '61'])).
% 1.18/1.44  thf('63', plain,
% 1.18/1.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.18/1.44         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.18/1.44           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.18/1.44      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.18/1.44  thf('64', plain,
% 1.18/1.44      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.18/1.44      inference('demod', [status(thm)], ['58', '59', '62', '63'])).
% 1.18/1.44  thf('65', plain,
% 1.18/1.44      (![X2 : $i, X4 : $i]:
% 1.18/1.44         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.18/1.44      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.18/1.44  thf('66', plain,
% 1.18/1.44      ((((k1_xboole_0) != (k1_xboole_0))
% 1.18/1.44        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 1.18/1.44      inference('sup-', [status(thm)], ['64', '65'])).
% 1.18/1.44  thf('67', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 1.18/1.44      inference('simplify', [status(thm)], ['66'])).
% 1.18/1.44  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 1.18/1.44  
% 1.18/1.44  % SZS output end Refutation
% 1.18/1.44  
% 1.27/1.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
