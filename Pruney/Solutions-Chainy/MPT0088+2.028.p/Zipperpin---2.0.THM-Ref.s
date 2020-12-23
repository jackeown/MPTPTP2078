%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.piVmnLC0K2

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:38 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 597 expanded)
%              Number of leaves         :   17 ( 208 expanded)
%              Depth                    :   28
%              Number of atoms          : 1221 (4730 expanded)
%              Number of equality atoms :  126 ( 549 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('60',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('67',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['69','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_A ) ) )
      = ( k4_xboole_0 @ sk_A @ X1 ) ) ),
    inference(demod,[status(thm)],['65','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('85',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('91',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_A )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('105',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['32','42','43','100','103','104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('110',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['1','110'])).

thf('112',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('115',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','82'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('121',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('122',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('124',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['0','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.piVmnLC0K2
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.67/2.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.67/2.86  % Solved by: fo/fo7.sh
% 2.67/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.86  % done 3195 iterations in 2.408s
% 2.67/2.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.67/2.86  % SZS output start Refutation
% 2.67/2.86  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.67/2.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.67/2.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.67/2.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.67/2.86  thf(sk_C_type, type, sk_C: $i).
% 2.67/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.67/2.86  thf(t81_xboole_1, conjecture,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.67/2.86       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 2.67/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.86    (~( ![A:$i,B:$i,C:$i]:
% 2.67/2.86        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 2.67/2.86          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 2.67/2.86    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 2.67/2.86  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(t48_xboole_1, axiom,
% 2.67/2.86    (![A:$i,B:$i]:
% 2.67/2.86     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.67/2.86  thf('1', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 2.67/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.86  thf(d7_xboole_0, axiom,
% 2.67/2.86    (![A:$i,B:$i]:
% 2.67/2.86     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.67/2.86       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.67/2.86  thf('3', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.67/2.86  thf('4', plain,
% 2.67/2.86      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 2.67/2.86      inference('sup-', [status(thm)], ['2', '3'])).
% 2.67/2.86  thf('5', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf(t49_xboole_1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.67/2.86       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.67/2.86  thf('6', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('7', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X2 @ 
% 2.67/2.86           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 2.67/2.86           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['5', '6'])).
% 2.67/2.86  thf('8', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('9', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X2 @ 
% 2.67/2.86           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 2.67/2.86           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['7', '8'])).
% 2.67/2.86  thf('10', plain,
% 2.67/2.86      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 2.67/2.86         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.67/2.86      inference('sup+', [status(thm)], ['4', '9'])).
% 2.67/2.86  thf(t3_boole, axiom,
% 2.67/2.86    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.67/2.86  thf('11', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('12', plain,
% 2.67/2.86      (((k3_xboole_0 @ sk_A @ sk_B)
% 2.67/2.86         = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.67/2.86      inference('demod', [status(thm)], ['10', '11'])).
% 2.67/2.86  thf('13', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf(t52_xboole_1, axiom,
% 2.67/2.86    (![A:$i,B:$i,C:$i]:
% 2.67/2.86     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.67/2.86       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.67/2.86  thf('14', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('15', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 2.67/2.86           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['13', '14'])).
% 2.67/2.86  thf('16', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('17', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ 
% 2.67/2.86           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 2.67/2.86           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['15', '16'])).
% 2.67/2.86  thf('18', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('19', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('20', plain,
% 2.67/2.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['18', '19'])).
% 2.67/2.86  thf(t2_boole, axiom,
% 2.67/2.86    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.67/2.86  thf('21', plain,
% 2.67/2.86      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.67/2.86      inference('cnf', [status(esa)], [t2_boole])).
% 2.67/2.86  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('demod', [status(thm)], ['20', '21'])).
% 2.67/2.86  thf('23', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('24', plain,
% 2.67/2.86      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['22', '23'])).
% 2.67/2.86  thf('25', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['24', '25'])).
% 2.67/2.86  thf('27', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('28', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.86           = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('sup+', [status(thm)], ['26', '27'])).
% 2.67/2.86  thf('29', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('30', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 2.67/2.86           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 2.67/2.86      inference('sup+', [status(thm)], ['28', '29'])).
% 2.67/2.86  thf('31', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ 
% 2.67/2.86           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 2.67/2.86           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['17', '30'])).
% 2.67/2.86  thf('32', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ 
% 2.67/2.86           (k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 2.67/2.86            (k3_xboole_0 @ sk_A @ sk_B)))
% 2.67/2.86           = (k4_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 2.67/2.86              sk_C))),
% 2.67/2.86      inference('sup+', [status(thm)], ['12', '31'])).
% 2.67/2.86  thf('33', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('34', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf(t39_xboole_1, axiom,
% 2.67/2.86    (![A:$i,B:$i]:
% 2.67/2.86     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.67/2.86  thf('35', plain,
% 2.67/2.86      (![X4 : $i, X5 : $i]:
% 2.67/2.86         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 2.67/2.86           = (k2_xboole_0 @ X4 @ X5))),
% 2.67/2.86      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.67/2.86  thf('36', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('sup+', [status(thm)], ['34', '35'])).
% 2.67/2.86  thf('37', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('demod', [status(thm)], ['20', '21'])).
% 2.67/2.86  thf('39', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['36', '37', '38'])).
% 2.67/2.86  thf('40', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('41', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['39', '40'])).
% 2.67/2.86  thf('42', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('sup+', [status(thm)], ['33', '41'])).
% 2.67/2.86  thf('43', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('44', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('45', plain,
% 2.67/2.86      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 2.67/2.86      inference('sup-', [status(thm)], ['2', '3'])).
% 2.67/2.86  thf('46', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('47', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('48', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['46', '47'])).
% 2.67/2.86  thf('49', plain,
% 2.67/2.86      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 2.67/2.86         = (k3_xboole_0 @ sk_A @ 
% 2.67/2.86            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.67/2.86      inference('sup+', [status(thm)], ['45', '48'])).
% 2.67/2.86  thf('50', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('51', plain,
% 2.67/2.86      (((sk_A)
% 2.67/2.86         = (k3_xboole_0 @ sk_A @ 
% 2.67/2.86            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.67/2.86      inference('demod', [status(thm)], ['49', '50'])).
% 2.67/2.86  thf('52', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('53', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ 
% 2.67/2.86           (k4_xboole_0 @ X0 @ 
% 2.67/2.86            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_A))),
% 2.67/2.86      inference('sup+', [status(thm)], ['51', '52'])).
% 2.67/2.86  thf('54', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['39', '40'])).
% 2.67/2.86  thf('55', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ 
% 2.67/2.86           (k4_xboole_0 @ X0 @ 
% 2.67/2.86            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))
% 2.67/2.86           = (sk_A))),
% 2.67/2.86      inference('demod', [status(thm)], ['53', '54'])).
% 2.67/2.86  thf(t79_xboole_1, axiom,
% 2.67/2.86    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.67/2.86  thf('56', plain,
% 2.67/2.86      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 2.67/2.86      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.67/2.86  thf('57', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         (r1_xboole_0 @ sk_A @ 
% 2.67/2.86          (k4_xboole_0 @ X0 @ 
% 2.67/2.86           (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.67/2.86      inference('sup+', [status(thm)], ['55', '56'])).
% 2.67/2.86  thf('58', plain,
% 2.67/2.86      (((sk_A)
% 2.67/2.86         = (k3_xboole_0 @ sk_A @ 
% 2.67/2.86            (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 2.67/2.86      inference('demod', [status(thm)], ['49', '50'])).
% 2.67/2.86  thf('59', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.86           = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('sup+', [status(thm)], ['26', '27'])).
% 2.67/2.86  thf('60', plain,
% 2.67/2.86      (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.67/2.86      inference('demod', [status(thm)], ['58', '59'])).
% 2.67/2.86  thf('61', plain,
% 2.67/2.86      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_A))),
% 2.67/2.86      inference('demod', [status(thm)], ['57', '60'])).
% 2.67/2.86  thf('62', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.67/2.86  thf('63', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 2.67/2.86      inference('sup-', [status(thm)], ['61', '62'])).
% 2.67/2.86  thf('64', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('65', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_A)))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X1) @ k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['63', '64'])).
% 2.67/2.86  thf('66', plain,
% 2.67/2.86      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.67/2.86      inference('cnf', [status(esa)], [t2_boole])).
% 2.67/2.86  thf('67', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('68', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('69', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 2.67/2.86           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['67', '68'])).
% 2.67/2.86  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('demod', [status(thm)], ['20', '21'])).
% 2.67/2.86  thf('71', plain,
% 2.67/2.86      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 2.67/2.86      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.67/2.86  thf('72', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.67/2.86  thf('73', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('sup-', [status(thm)], ['71', '72'])).
% 2.67/2.86  thf('74', plain,
% 2.67/2.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['70', '73'])).
% 2.67/2.86  thf('75', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('76', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['74', '75'])).
% 2.67/2.86  thf('77', plain,
% 2.67/2.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['70', '73'])).
% 2.67/2.86  thf('78', plain,
% 2.67/2.86      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['76', '77'])).
% 2.67/2.86  thf('79', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('80', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.67/2.86      inference('demod', [status(thm)], ['69', '78', '79'])).
% 2.67/2.86  thf('81', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['66', '80'])).
% 2.67/2.86  thf('82', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_A)))
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['65', '81'])).
% 2.67/2.86  thf('83', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['44', '82'])).
% 2.67/2.86  thf('84', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['24', '25'])).
% 2.67/2.86  thf('85', plain,
% 2.67/2.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 2.67/2.86              (k3_xboole_0 @ X12 @ X14)))),
% 2.67/2.86      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.67/2.86  thf('86', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['84', '85'])).
% 2.67/2.86  thf('87', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.67/2.86      inference('demod', [status(thm)], ['39', '40'])).
% 2.67/2.86  thf('88', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['86', '87'])).
% 2.67/2.86  thf('89', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ sk_A @ X0))
% 2.67/2.86           = (k3_xboole_0 @ X0 @ sk_A))),
% 2.67/2.86      inference('sup+', [status(thm)], ['83', '88'])).
% 2.67/2.86  thf('90', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('91', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('92', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ X0))
% 2.67/2.86           = (k3_xboole_0 @ X0 @ sk_A))),
% 2.67/2.86      inference('demod', [status(thm)], ['89', '90', '91'])).
% 2.67/2.86  thf('93', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('94', plain,
% 2.67/2.86      (![X7 : $i, X8 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 2.67/2.86           = (k3_xboole_0 @ X7 @ X8))),
% 2.67/2.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.86  thf('95', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['93', '94'])).
% 2.67/2.86  thf('96', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.67/2.86           = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.86      inference('sup+', [status(thm)], ['26', '27'])).
% 2.67/2.86  thf('97', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k4_xboole_0 @ X1 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['95', '96'])).
% 2.67/2.86  thf('98', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ sk_A))
% 2.67/2.86           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['92', '97'])).
% 2.67/2.86  thf('99', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k4_xboole_0 @ X1 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['95', '96'])).
% 2.67/2.86  thf('100', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ sk_A)
% 2.67/2.86           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ X0)))),
% 2.67/2.86      inference('demod', [status(thm)], ['98', '99'])).
% 2.67/2.86  thf('101', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['86', '87'])).
% 2.67/2.86  thf('102', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 2.67/2.86      inference('sup-', [status(thm)], ['71', '72'])).
% 2.67/2.86  thf('103', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['101', '102'])).
% 2.67/2.86  thf('104', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('105', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('106', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k1_xboole_0)
% 2.67/2.86           = (k3_xboole_0 @ sk_A @ 
% 2.67/2.86              (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 2.67/2.86      inference('demod', [status(thm)],
% 2.67/2.86                ['32', '42', '43', '100', '103', '104', '105'])).
% 2.67/2.86  thf('107', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k4_xboole_0 @ X1 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['95', '96'])).
% 2.67/2.86  thf('108', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ 
% 2.67/2.86              (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['106', '107'])).
% 2.67/2.86  thf('109', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 2.67/2.86      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.86  thf('110', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((sk_A)
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ 
% 2.67/2.86              (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 2.67/2.86      inference('demod', [status(thm)], ['108', '109'])).
% 2.67/2.86  thf('111', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((sk_A)
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ 
% 2.67/2.86              (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C)))),
% 2.67/2.86      inference('sup+', [status(thm)], ['1', '110'])).
% 2.67/2.86  thf('112', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('113', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((sk_A)
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ 
% 2.67/2.86              (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))))),
% 2.67/2.86      inference('demod', [status(thm)], ['111', '112'])).
% 2.67/2.86  thf('114', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X2 @ 
% 2.67/2.86           (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 2.67/2.86           = (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['7', '8'])).
% 2.67/2.86  thf('115', plain,
% 2.67/2.86      (((k3_xboole_0 @ sk_B @ sk_A)
% 2.67/2.86         = (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 2.67/2.86      inference('sup+', [status(thm)], ['113', '114'])).
% 2.67/2.86  thf('116', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.67/2.86           = (k4_xboole_0 @ X1 @ X0))),
% 2.67/2.86      inference('demod', [status(thm)], ['95', '96'])).
% 2.67/2.86  thf('117', plain,
% 2.67/2.86      (((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 2.67/2.86         (k3_xboole_0 @ sk_B @ sk_A))
% 2.67/2.86         = (k4_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C))),
% 2.67/2.86      inference('sup+', [status(thm)], ['115', '116'])).
% 2.67/2.86  thf('118', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('119', plain,
% 2.67/2.86      (![X0 : $i]:
% 2.67/2.86         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_A))
% 2.67/2.86           = (k4_xboole_0 @ sk_A @ X0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['44', '82'])).
% 2.67/2.86  thf('120', plain,
% 2.67/2.86      (![X0 : $i, X1 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.67/2.86      inference('sup+', [status(thm)], ['101', '102'])).
% 2.67/2.86  thf('121', plain,
% 2.67/2.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.86         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 2.67/2.86           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 2.67/2.86      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.67/2.86  thf('122', plain,
% 2.67/2.86      (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.67/2.86      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 2.67/2.86  thf('123', plain,
% 2.67/2.86      (![X0 : $i, X2 : $i]:
% 2.67/2.86         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 2.67/2.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.67/2.86  thf('124', plain,
% 2.67/2.86      ((((k1_xboole_0) != (k1_xboole_0))
% 2.67/2.86        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 2.67/2.86      inference('sup-', [status(thm)], ['122', '123'])).
% 2.67/2.86  thf('125', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 2.67/2.86      inference('simplify', [status(thm)], ['124'])).
% 2.67/2.86  thf('126', plain, ($false), inference('demod', [status(thm)], ['0', '125'])).
% 2.67/2.86  
% 2.67/2.86  % SZS output end Refutation
% 2.67/2.86  
% 2.67/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
