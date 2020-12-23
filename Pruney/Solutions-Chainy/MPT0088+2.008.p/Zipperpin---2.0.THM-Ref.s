%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yWkYPl2r3o

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:35 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 163 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  710 (1272 expanded)
%              Number of equality atoms :   77 ( 148 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['20','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yWkYPl2r3o
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:52:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 426 iterations in 0.149s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.59  thf(t48_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf(t81_xboole_1, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.59       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.59        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.59          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.37/0.59  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d7_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X2 : $i, X3 : $i]:
% 0.37/0.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(t50_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.37/0.59       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.37/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.37/0.59              (k3_xboole_0 @ X16 @ X18)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.37/0.59  thf(t49_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.37/0.59       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.37/0.59           = (k3_xboole_0 @ X16 @ 
% 0.37/0.59              (k4_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X18))))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ sk_A @ 
% 0.37/0.59           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.37/0.59           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['3', '6'])).
% 0.37/0.59  thf(t3_boole, axiom,
% 0.37/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.59  thf('8', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ sk_A @ 
% 0.37/0.59           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.37/0.59           = (k3_xboole_0 @ sk_A @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.37/0.59         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.59      inference('sup+', [status(thm)], ['0', '9'])).
% 0.37/0.59  thf(t47_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.37/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.37/0.59         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.37/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.37/0.59         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.37/0.59           = (k3_xboole_0 @ X16 @ 
% 0.37/0.59              (k4_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X18))))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.37/0.59         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (![X2 : $i, X4 : $i]:
% 0.37/0.59         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      ((((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))
% 0.37/0.59        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf('19', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.37/0.59      inference('clc', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('22', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf(t2_boole, axiom,
% 0.37/0.59    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.59  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['26', '27'])).
% 0.37/0.59  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.37/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.59  thf('30', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.37/0.59           = (k4_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['30', '31'])).
% 0.37/0.59  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.59  thf(t39_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.37/0.59           = (k2_xboole_0 @ X6 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.59           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 0.37/0.59           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.59      inference('sup+', [status(thm)], ['33', '36'])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.59  thf('39', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.59  thf(t51_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.37/0.59       ( A ) ))).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.59           = (X19))),
% 0.37/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.59  thf('41', plain,
% 0.37/0.59      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.59  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.37/0.59  thf(t52_xboole_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.37/0.59       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.37/0.59              (k3_xboole_0 @ X21 @ X23)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.59  thf('47', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.37/0.59           = (X19))),
% 0.37/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k2_xboole_0 @ 
% 0.37/0.59           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))) @ 
% 0.37/0.59           (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['46', '47'])).
% 0.37/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.37/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ 
% 0.37/0.59              (k3_xboole_0 @ X21 @ X23)))),
% 0.37/0.59      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.37/0.59  thf('51', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.37/0.59           = (X1))),
% 0.37/0.59      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.37/0.59  thf('53', plain,
% 0.37/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.37/0.59           = (k3_xboole_0 @ X16 @ 
% 0.37/0.59              (k4_xboole_0 @ X17 @ (k3_xboole_0 @ X16 @ X18))))),
% 0.37/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.37/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.37/0.59      inference('sup+', [status(thm)], ['52', '53'])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X11 : $i, X12 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.37/0.59           = (k3_xboole_0 @ X11 @ X12))),
% 0.37/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.37/0.59           = (k3_xboole_0 @ X1 @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.59           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['32', '56'])).
% 0.37/0.59  thf('58', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.37/0.59      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.59  thf('59', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X1 @ X0)
% 0.37/0.59           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.59  thf('60', plain,
% 0.37/0.59      (![X9 : $i, X10 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.37/0.59           = (k4_xboole_0 @ X9 @ X10))),
% 0.37/0.59      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.37/0.59  thf('61', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.59           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['59', '60'])).
% 0.37/0.59  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.59  thf('63', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('demod', [status(thm)], ['61', '62'])).
% 0.37/0.59  thf('64', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.37/0.59      inference('sup+', [status(thm)], ['21', '63'])).
% 0.37/0.59  thf('65', plain,
% 0.37/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.59         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.37/0.59           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.37/0.59      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.37/0.59  thf('66', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.37/0.59      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.59  thf('67', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['20', '66'])).
% 0.37/0.59  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
