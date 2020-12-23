%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UnWACg2RPR

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:23 EST 2020

% Result     : Theorem 29.07s
% Output     : Refutation 29.07s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 280 expanded)
%              Number of leaves         :   16 ( 100 expanded)
%              Depth                    :   18
%              Number of atoms          :  761 (2184 expanded)
%              Number of equality atoms :   82 ( 273 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t55_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf('28',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ X8 )
      = ( k4_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UnWACg2RPR
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.07/29.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.07/29.32  % Solved by: fo/fo7.sh
% 29.07/29.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.07/29.32  % done 9131 iterations in 28.855s
% 29.07/29.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.07/29.32  % SZS output start Refutation
% 29.07/29.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.07/29.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.07/29.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.07/29.32  thf(sk_A_type, type, sk_A: $i).
% 29.07/29.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.07/29.32  thf(sk_B_type, type, sk_B: $i).
% 29.07/29.32  thf(t55_xboole_1, conjecture,
% 29.07/29.32    (![A:$i,B:$i]:
% 29.07/29.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 29.07/29.32       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 29.07/29.32  thf(zf_stmt_0, negated_conjecture,
% 29.07/29.32    (~( ![A:$i,B:$i]:
% 29.07/29.32        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 29.07/29.32          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 29.07/29.32    inference('cnf.neg', [status(esa)], [t55_xboole_1])).
% 29.07/29.32  thf('0', plain,
% 29.07/29.32      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 29.07/29.32         (k3_xboole_0 @ sk_A @ sk_B))
% 29.07/29.32         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 29.07/29.32             (k4_xboole_0 @ sk_B @ sk_A)))),
% 29.07/29.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.07/29.32  thf(t48_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i]:
% 29.07/29.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 29.07/29.32  thf('1', plain,
% 29.07/29.32      (![X15 : $i, X16 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 29.07/29.32           = (k3_xboole_0 @ X15 @ X16))),
% 29.07/29.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.07/29.32  thf('2', plain,
% 29.07/29.32      (![X15 : $i, X16 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 29.07/29.32           = (k3_xboole_0 @ X15 @ X16))),
% 29.07/29.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.07/29.32  thf('3', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['1', '2'])).
% 29.07/29.32  thf(t51_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i]:
% 29.07/29.32     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 29.07/29.32       ( A ) ))).
% 29.07/29.32  thf('4', plain,
% 29.07/29.32      (![X17 : $i, X18 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 29.07/29.32           = (X17))),
% 29.07/29.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.07/29.32  thf(commutativity_k2_xboole_0, axiom,
% 29.07/29.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 29.07/29.32  thf('5', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.07/29.32  thf(t3_boole, axiom,
% 29.07/29.32    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 29.07/29.32  thf('6', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 29.07/29.32      inference('cnf', [status(esa)], [t3_boole])).
% 29.07/29.32  thf('7', plain,
% 29.07/29.32      (![X15 : $i, X16 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 29.07/29.32           = (k3_xboole_0 @ X15 @ X16))),
% 29.07/29.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.07/29.32  thf('8', plain,
% 29.07/29.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['6', '7'])).
% 29.07/29.32  thf(commutativity_k3_xboole_0, axiom,
% 29.07/29.32    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 29.07/29.32  thf('9', plain,
% 29.07/29.32      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.07/29.32  thf('10', plain,
% 29.07/29.32      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['8', '9'])).
% 29.07/29.32  thf('11', plain,
% 29.07/29.32      (![X17 : $i, X18 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 29.07/29.32           = (X17))),
% 29.07/29.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.07/29.32  thf('12', plain,
% 29.07/29.32      (![X0 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 29.07/29.32           (k4_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['10', '11'])).
% 29.07/29.32  thf(t42_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i,C:$i]:
% 29.07/29.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 29.07/29.32       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 29.07/29.32  thf('13', plain,
% 29.07/29.32      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X14) @ X13)
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 29.07/29.32              (k4_xboole_0 @ X14 @ X13)))),
% 29.07/29.32      inference('cnf', [status(esa)], [t42_xboole_1])).
% 29.07/29.32  thf(t40_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i]:
% 29.07/29.32     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 29.07/29.32  thf('14', plain,
% 29.07/29.32      (![X7 : $i, X8 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 29.07/29.32           = (k4_xboole_0 @ X7 @ X8))),
% 29.07/29.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.07/29.32  thf('15', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 29.07/29.32      inference('cnf', [status(esa)], [t3_boole])).
% 29.07/29.32  thf('16', plain,
% 29.07/29.32      (![X0 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['14', '15'])).
% 29.07/29.32  thf('17', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 29.07/29.32      inference('cnf', [status(esa)], [t3_boole])).
% 29.07/29.32  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['16', '17'])).
% 29.07/29.32  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.07/29.32      inference('demod', [status(thm)], ['12', '13', '18'])).
% 29.07/29.32  thf(t41_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i,C:$i]:
% 29.07/29.32     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 29.07/29.32       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 29.07/29.32  thf('20', plain,
% 29.07/29.32      (![X9 : $i, X10 : $i, X11 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 29.07/29.32           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 29.07/29.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 29.07/29.32  thf('21', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 29.07/29.32           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['19', '20'])).
% 29.07/29.32  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['16', '17'])).
% 29.07/29.32  thf('23', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.07/29.32  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['22', '23'])).
% 29.07/29.32  thf('25', plain,
% 29.07/29.32      (![X7 : $i, X8 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 29.07/29.32           = (k4_xboole_0 @ X7 @ X8))),
% 29.07/29.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.07/29.32  thf('26', plain,
% 29.07/29.32      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['24', '25'])).
% 29.07/29.32  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.07/29.32      inference('demod', [status(thm)], ['12', '13', '18'])).
% 29.07/29.32  thf('28', plain,
% 29.07/29.32      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 29.07/29.32      inference('demod', [status(thm)], ['26', '27'])).
% 29.07/29.32  thf('29', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('demod', [status(thm)], ['21', '28'])).
% 29.07/29.32  thf('30', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['5', '29'])).
% 29.07/29.32  thf('31', plain,
% 29.07/29.32      (![X15 : $i, X16 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 29.07/29.32           = (k3_xboole_0 @ X15 @ X16))),
% 29.07/29.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 29.07/29.32  thf('32', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 29.07/29.32           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['30', '31'])).
% 29.07/29.32  thf('33', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 29.07/29.32      inference('cnf', [status(esa)], [t3_boole])).
% 29.07/29.32  thf('34', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('demod', [status(thm)], ['32', '33'])).
% 29.07/29.32  thf('35', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X0 @ X1)
% 29.07/29.32           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['4', '34'])).
% 29.07/29.32  thf('36', plain,
% 29.07/29.32      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.07/29.32  thf('37', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X0 @ X1)
% 29.07/29.32           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 29.07/29.32      inference('demod', [status(thm)], ['35', '36'])).
% 29.07/29.32  thf('38', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k4_xboole_0 @ X1 @ X0))),
% 29.07/29.32      inference('demod', [status(thm)], ['3', '37'])).
% 29.07/29.32  thf('39', plain,
% 29.07/29.32      (![X7 : $i, X8 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 29.07/29.32           = (k4_xboole_0 @ X7 @ X8))),
% 29.07/29.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.07/29.32  thf('40', plain,
% 29.07/29.32      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X14) @ X13)
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 29.07/29.32              (k4_xboole_0 @ X14 @ X13)))),
% 29.07/29.32      inference('cnf', [status(esa)], [t42_xboole_1])).
% 29.07/29.32  thf('41', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X0)
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['39', '40'])).
% 29.07/29.32  thf('42', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ 
% 29.07/29.32           (k2_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1) @ 
% 29.07/29.32           (k3_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 29.07/29.32              (k4_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['38', '41'])).
% 29.07/29.32  thf('43', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.07/29.32  thf('44', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.07/29.32  thf('45', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ 
% 29.07/29.32           (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 29.07/29.32           (k3_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 29.07/29.32              (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 29.07/29.32      inference('demod', [status(thm)], ['42', '43', '44'])).
% 29.07/29.32  thf('46', plain,
% 29.07/29.32      (![X17 : $i, X18 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 29.07/29.32           = (X17))),
% 29.07/29.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.07/29.32  thf('47', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('demod', [status(thm)], ['21', '28'])).
% 29.07/29.32  thf('48', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['46', '47'])).
% 29.07/29.32  thf('49', plain,
% 29.07/29.32      (![X12 : $i, X13 : $i, X14 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X14) @ X13)
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 29.07/29.32              (k4_xboole_0 @ X14 @ X13)))),
% 29.07/29.32      inference('cnf', [status(esa)], [t42_xboole_1])).
% 29.07/29.32  thf('50', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ k1_xboole_0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['48', '49'])).
% 29.07/29.32  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['16', '17'])).
% 29.07/29.32  thf('52', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 29.07/29.32           = (k4_xboole_0 @ X2 @ X0))),
% 29.07/29.32      inference('demod', [status(thm)], ['50', '51'])).
% 29.07/29.32  thf(t39_xboole_1, axiom,
% 29.07/29.32    (![A:$i,B:$i]:
% 29.07/29.32     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 29.07/29.32  thf('53', plain,
% 29.07/29.32      (![X4 : $i, X5 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 29.07/29.32           = (k2_xboole_0 @ X4 @ X5))),
% 29.07/29.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 29.07/29.32  thf('54', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))))),
% 29.07/29.32      inference('sup+', [status(thm)], ['52', '53'])).
% 29.07/29.32  thf('55', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.07/29.32      inference('demod', [status(thm)], ['32', '33'])).
% 29.07/29.32  thf('56', plain,
% 29.07/29.32      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 29.07/29.32  thf('57', plain,
% 29.07/29.32      (![X17 : $i, X18 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 29.07/29.32           = (X17))),
% 29.07/29.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.07/29.32  thf('58', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 29.07/29.32           = (X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['56', '57'])).
% 29.07/29.32  thf('59', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))
% 29.07/29.32           = (k2_xboole_0 @ X1 @ X0))),
% 29.07/29.32      inference('sup+', [status(thm)], ['55', '58'])).
% 29.07/29.32  thf('60', plain,
% 29.07/29.32      (![X7 : $i, X8 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ X8)
% 29.07/29.32           = (k4_xboole_0 @ X7 @ X8))),
% 29.07/29.32      inference('cnf', [status(esa)], [t40_xboole_1])).
% 29.07/29.32  thf('61', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ X1 @ X0))),
% 29.07/29.32      inference('demod', [status(thm)], ['59', '60'])).
% 29.07/29.32  thf('62', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X1 @ X0)
% 29.07/29.32           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))))),
% 29.07/29.32      inference('demod', [status(thm)], ['54', '61'])).
% 29.07/29.32  thf('63', plain,
% 29.07/29.32      (![X17 : $i, X18 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 29.07/29.32           = (X17))),
% 29.07/29.32      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.07/29.32  thf('64', plain,
% 29.07/29.32      (![X9 : $i, X10 : $i, X11 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 29.07/29.32           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 29.07/29.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 29.07/29.32  thf('65', plain,
% 29.07/29.32      (![X4 : $i, X5 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 29.07/29.32           = (k2_xboole_0 @ X4 @ X5))),
% 29.07/29.32      inference('cnf', [status(esa)], [t39_xboole_1])).
% 29.07/29.32  thf('66', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 29.07/29.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 29.07/29.32      inference('sup+', [status(thm)], ['64', '65'])).
% 29.07/29.32  thf('67', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 29.07/29.32              (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))))),
% 29.07/29.32      inference('sup+', [status(thm)], ['63', '66'])).
% 29.07/29.32  thf('68', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.07/29.32         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 29.07/29.32           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 29.07/29.32      inference('demod', [status(thm)], ['45', '62', '67'])).
% 29.07/29.32  thf('69', plain,
% 29.07/29.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.07/29.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.07/29.32  thf('70', plain,
% 29.07/29.32      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 29.07/29.32         (k3_xboole_0 @ sk_A @ sk_B))
% 29.07/29.32         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 29.07/29.32             (k3_xboole_0 @ sk_A @ sk_B)))),
% 29.07/29.32      inference('demod', [status(thm)], ['0', '68', '69'])).
% 29.07/29.32  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 29.07/29.32  
% 29.07/29.32  % SZS output end Refutation
% 29.07/29.32  
% 29.07/29.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
