%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.euHRKWhuI3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 228 expanded)
%              Number of leaves         :   20 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  734 (1722 expanded)
%              Number of equality atoms :   81 ( 206 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
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

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['17','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['4','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['50','51','52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','41'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['50','51','52','60'])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['63','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['3','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.euHRKWhuI3
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.92/1.10  % Solved by: fo/fo7.sh
% 0.92/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.10  % done 1621 iterations in 0.637s
% 0.92/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.92/1.10  % SZS output start Refutation
% 0.92/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.92/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.92/1.10  thf(t76_xboole_1, conjecture,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( r1_xboole_0 @ A @ B ) =>
% 0.92/1.10       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.92/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.10        ( ( r1_xboole_0 @ A @ B ) =>
% 0.92/1.10          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.92/1.10    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.92/1.10  thf('0', plain,
% 0.92/1.10      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.92/1.10          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(commutativity_k3_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.92/1.10  thf('1', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf('2', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf('3', plain,
% 0.92/1.10      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.92/1.10          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.92/1.10      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.92/1.10  thf(t48_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.92/1.10  thf('4', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.92/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.10  thf(d7_xboole_0, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.92/1.10       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.92/1.10  thf('6', plain,
% 0.92/1.10      (![X2 : $i, X3 : $i]:
% 0.92/1.10         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.92/1.10      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.92/1.10  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['5', '6'])).
% 0.92/1.10  thf('8', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf(t47_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.92/1.10  thf('9', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.92/1.10           = (k4_xboole_0 @ X14 @ X15))),
% 0.92/1.10      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.92/1.10  thf('10', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k4_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('sup+', [status(thm)], ['8', '9'])).
% 0.92/1.10  thf('11', plain,
% 0.92/1.10      (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.92/1.10      inference('sup+', [status(thm)], ['7', '10'])).
% 0.92/1.10  thf(t3_boole, axiom,
% 0.92/1.10    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.92/1.10  thf('12', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.10  thf('13', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 0.92/1.10      inference('demod', [status(thm)], ['11', '12'])).
% 0.92/1.10  thf('14', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf(t52_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.92/1.10       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.92/1.10  thf('15', plain,
% 0.92/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.92/1.10              (k3_xboole_0 @ X20 @ X22)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.92/1.10  thf('16', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['14', '15'])).
% 0.92/1.10  thf('17', plain,
% 0.92/1.10      (![X0 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.92/1.10           = (k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['13', '16'])).
% 0.92/1.10  thf('18', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf('19', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.92/1.10           = (k4_xboole_0 @ X14 @ X15))),
% 0.92/1.10      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.92/1.10  thf(t39_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.92/1.10  thf('20', plain,
% 0.92/1.10      (![X6 : $i, X7 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.92/1.10           = (k2_xboole_0 @ X6 @ X7))),
% 0.92/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.92/1.10  thf('21', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.92/1.10      inference('sup+', [status(thm)], ['19', '20'])).
% 0.92/1.10  thf(t51_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.92/1.10       ( A ) ))).
% 0.92/1.10  thf('22', plain,
% 0.92/1.10      (![X18 : $i, X19 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.92/1.10           = (X18))),
% 0.92/1.10      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.92/1.10  thf('23', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['21', '22'])).
% 0.92/1.10  thf('24', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['18', '23'])).
% 0.92/1.10  thf(t46_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.92/1.10  thf('25', plain,
% 0.92/1.10      (![X12 : $i, X13 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.92/1.10  thf('26', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['24', '25'])).
% 0.92/1.10  thf('27', plain,
% 0.92/1.10      (![X6 : $i, X7 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.92/1.10           = (k2_xboole_0 @ X6 @ X7))),
% 0.92/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.92/1.10  thf('28', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.92/1.10           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['26', '27'])).
% 0.92/1.10  thf('29', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.10  thf('30', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('31', plain,
% 0.92/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['29', '30'])).
% 0.92/1.10  thf(t2_boole, axiom,
% 0.92/1.10    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.92/1.10  thf('32', plain,
% 0.92/1.10      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.10      inference('cnf', [status(esa)], [t2_boole])).
% 0.92/1.10  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('demod', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('34', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('35', plain,
% 0.92/1.10      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['33', '34'])).
% 0.92/1.10  thf('36', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.10  thf('37', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['35', '36'])).
% 0.92/1.10  thf('38', plain,
% 0.92/1.10      (![X18 : $i, X19 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 0.92/1.10           = (X18))),
% 0.92/1.10      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.92/1.10  thf('39', plain,
% 0.92/1.10      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['37', '38'])).
% 0.92/1.10  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('demod', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.92/1.10      inference('demod', [status(thm)], ['39', '40'])).
% 0.92/1.10  thf('42', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['28', '41'])).
% 0.92/1.10  thf('43', plain,
% 0.92/1.10      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 0.92/1.10      inference('demod', [status(thm)], ['17', '42'])).
% 0.92/1.10  thf('44', plain,
% 0.92/1.10      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 0.92/1.10      inference('sup+', [status(thm)], ['4', '43'])).
% 0.92/1.10  thf('45', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf('46', plain,
% 0.92/1.10      (![X14 : $i, X15 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.92/1.10           = (k4_xboole_0 @ X14 @ X15))),
% 0.92/1.10      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.92/1.10  thf('47', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('48', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['46', '47'])).
% 0.92/1.10  thf('49', plain,
% 0.92/1.10      (![X6 : $i, X7 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.92/1.10           = (k2_xboole_0 @ X6 @ X7))),
% 0.92/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.92/1.10  thf('50', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.92/1.10           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.92/1.10      inference('sup+', [status(thm)], ['48', '49'])).
% 0.92/1.10  thf('51', plain,
% 0.92/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.92/1.10              (k3_xboole_0 @ X20 @ X22)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.92/1.10  thf('52', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k4_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('sup+', [status(thm)], ['8', '9'])).
% 0.92/1.10  thf('53', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('54', plain,
% 0.92/1.10      (![X6 : $i, X7 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 0.92/1.10           = (k2_xboole_0 @ X6 @ X7))),
% 0.92/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.92/1.10  thf('55', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.92/1.10      inference('sup+', [status(thm)], ['53', '54'])).
% 0.92/1.10  thf('56', plain,
% 0.92/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ 
% 0.92/1.10              (k3_xboole_0 @ X20 @ X22)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.92/1.10  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('demod', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('58', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.92/1.10           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.92/1.10  thf('59', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.92/1.10      inference('cnf', [status(esa)], [t3_boole])).
% 0.92/1.10  thf('60', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X1) = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['58', '59'])).
% 0.92/1.10  thf('61', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['50', '51', '52', '60'])).
% 0.92/1.10  thf('62', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['28', '41'])).
% 0.92/1.10  thf(t41_xboole_1, axiom,
% 0.92/1.10    (![A:$i,B:$i,C:$i]:
% 0.92/1.10     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.92/1.10       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.92/1.10  thf('63', plain,
% 0.92/1.10      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.92/1.10           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.92/1.10      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.92/1.10  thf('64', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 0.92/1.10      inference('demod', [status(thm)], ['50', '51', '52', '60'])).
% 0.92/1.10  thf('65', plain,
% 0.92/1.10      (![X16 : $i, X17 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.92/1.10           = (k3_xboole_0 @ X16 @ X17))),
% 0.92/1.10      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.92/1.10  thf('66', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k4_xboole_0 @ X0 @ X0)
% 0.92/1.10           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['64', '65'])).
% 0.92/1.10  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.92/1.10      inference('demod', [status(thm)], ['31', '32'])).
% 0.92/1.10  thf('68', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('demod', [status(thm)], ['66', '67'])).
% 0.92/1.10  thf('69', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.92/1.10  thf('70', plain,
% 0.92/1.10      (![X2 : $i, X4 : $i]:
% 0.92/1.10         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.92/1.10      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.92/1.10  thf('71', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.92/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.92/1.10  thf('72', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         (((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.10          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.92/1.10      inference('sup-', [status(thm)], ['68', '71'])).
% 0.92/1.10  thf('73', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.92/1.10      inference('simplify', [status(thm)], ['72'])).
% 0.92/1.10  thf('74', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 0.92/1.10      inference('sup+', [status(thm)], ['63', '73'])).
% 0.92/1.10  thf('75', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['62', '74'])).
% 0.92/1.10  thf('76', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.92/1.10      inference('sup+', [status(thm)], ['61', '75'])).
% 0.92/1.10  thf('77', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.92/1.10         (r1_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['45', '76'])).
% 0.92/1.10  thf('78', plain,
% 0.92/1.10      (![X0 : $i, X1 : $i]:
% 0.92/1.10         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X1) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.92/1.10      inference('sup+', [status(thm)], ['44', '77'])).
% 0.92/1.10  thf('79', plain, ($false), inference('demod', [status(thm)], ['3', '78'])).
% 0.92/1.10  
% 0.92/1.10  % SZS output end Refutation
% 0.92/1.10  
% 0.92/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
