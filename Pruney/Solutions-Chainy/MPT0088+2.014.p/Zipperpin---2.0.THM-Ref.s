%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P0ZVTgXCuC

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:36 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 236 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  850 (1888 expanded)
%              Number of equality atoms :   90 ( 212 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
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
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6','11'])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['23','28'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','84'])).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['40','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P0ZVTgXCuC
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:19:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 819 iterations in 0.452s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(t81_xboole_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.71/0.90       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.90        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.71/0.90          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.71/0.90  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf(t48_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf(t39_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.71/0.90           = (k2_xboole_0 @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['3', '4'])).
% 0.71/0.90  thf(t52_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.71/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.71/0.90              (k3_xboole_0 @ X16 @ X18)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.71/0.90  thf(t3_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.90  thf('7', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.71/0.90  thf(t2_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.90  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.71/0.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['5', '6', '11'])).
% 0.71/0.90  thf('13', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('demod', [status(thm)], ['12', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['2', '14'])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['1', '15'])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.71/0.90           = (k2_xboole_0 @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.90  thf('19', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d7_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.71/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.71/0.90  thf(t51_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.71/0.90       ( A ) ))).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.71/0.90           = (X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (((k2_xboole_0 @ k1_xboole_0 @ 
% 0.71/0.90         (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))) = (sk_A))),
% 0.71/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.71/0.90           = (X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('27', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '27'])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['23', '28'])).
% 0.71/0.90  thf(t41_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.71/0.90       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ sk_A @ X0)
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.71/0.90              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ sk_A @ 
% 0.71/0.90           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.71/0.90              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['18', '31'])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ sk_A @ X0)
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.71/0.90              (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['29', '30'])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ sk_A @ 
% 0.71/0.90           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['32', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.71/0.90         = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['17', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.71/0.90              (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['35', '36'])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.71/0.90           = (k4_xboole_0 @ sk_A @ 
% 0.71/0.90              (k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.71/0.90         = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.71/0.90      inference('sup+', [status(thm)], ['16', '39'])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.71/0.90           = (k2_xboole_0 @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.71/0.90           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['41', '42'])).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.71/0.90           = (k4_xboole_0 @ X2 @ 
% 0.71/0.90              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['44', '45'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.71/0.90           = (k4_xboole_0 @ X2 @ 
% 0.71/0.90              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.71/0.90      inference('demod', [status(thm)], ['46', '47'])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.71/0.90           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['43', '48'])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.71/0.90           = (k2_xboole_0 @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.71/0.90  thf('53', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.71/0.90           = (k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['53', '54'])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X6 : $i, X7 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.71/0.90           = (k2_xboole_0 @ X6 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '56'])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['52', '57'])).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.71/0.90           = (X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.90  thf('60', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ k1_xboole_0 @ 
% 0.71/0.90           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['58', '59'])).
% 0.71/0.90  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '27'])).
% 0.71/0.90  thf('62', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['60', '61'])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['55', '56'])).
% 0.71/0.90  thf('64', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.71/0.90           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['41', '42'])).
% 0.71/0.90  thf('65', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 0.71/0.90           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['63', '64'])).
% 0.71/0.90  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.90  thf('67', plain,
% 0.71/0.90      (![X12 : $i, X13 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.71/0.90           = (k3_xboole_0 @ X12 @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['66', '67'])).
% 0.71/0.90  thf('69', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('70', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ (k4_xboole_0 @ X14 @ X15))
% 0.71/0.90           = (X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['70', '71'])).
% 0.71/0.90  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.90  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['72', '73'])).
% 0.71/0.90  thf('75', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('demod', [status(thm)], ['65', '74'])).
% 0.71/0.90  thf('76', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('77', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['52', '57'])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('79', plain,
% 0.71/0.90      (![X2 : $i, X4 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('80', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['78', '79'])).
% 0.71/0.90  thf('81', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.71/0.90          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['77', '80'])).
% 0.71/0.90  thf('82', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.71/0.90      inference('simplify', [status(thm)], ['81'])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 0.71/0.90      inference('sup+', [status(thm)], ['76', '82'])).
% 0.71/0.90  thf('84', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['75', '83'])).
% 0.71/0.90  thf('85', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['62', '84'])).
% 0.71/0.90  thf('86', plain,
% 0.71/0.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.71/0.90           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.71/0.90  thf('87', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.71/0.90      inference('demod', [status(thm)], ['85', '86'])).
% 0.71/0.90  thf('88', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.71/0.90      inference('sup+', [status(thm)], ['40', '87'])).
% 0.71/0.90  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
