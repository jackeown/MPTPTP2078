%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdirhVn48e

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:13 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  117 (5530 expanded)
%              Number of leaves         :   17 (1896 expanded)
%              Depth                    :   31
%              Number of atoms          :  968 (51535 expanded)
%              Number of equality atoms :  109 (5522 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['11','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['4','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','58'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64','69','70'])).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ X10 @ X11 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('86',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['11','52'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','96'])).

thf('98',plain,(
    $false ),
    inference(simplify,[status(thm)],['97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdirhVn48e
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:28:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.21/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.39  % Solved by: fo/fo7.sh
% 1.21/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.39  % done 1814 iterations in 0.948s
% 1.21/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.39  % SZS output start Refutation
% 1.21/1.39  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.21/1.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.21/1.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.21/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.21/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.39  thf(t100_xboole_1, conjecture,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.39    (~( ![A:$i,B:$i]:
% 1.21/1.39        ( ( k4_xboole_0 @ A @ B ) =
% 1.21/1.39          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.21/1.39    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 1.21/1.39  thf('0', plain,
% 1.21/1.39      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.21/1.39         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.21/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.39  thf(commutativity_k3_xboole_0, axiom,
% 1.21/1.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.21/1.39  thf('1', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf('2', plain,
% 1.21/1.39      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.21/1.39         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.21/1.39      inference('demod', [status(thm)], ['0', '1'])).
% 1.21/1.39  thf('3', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf(t5_boole, axiom,
% 1.21/1.39    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.21/1.39  thf('4', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.21/1.39      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.39  thf('5', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf(t47_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.21/1.39  thf('6', plain,
% 1.21/1.39      (![X12 : $i, X13 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.21/1.39           = (k4_xboole_0 @ X12 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.21/1.39  thf('7', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('sup+', [status(thm)], ['5', '6'])).
% 1.21/1.39  thf(d6_xboole_0, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k5_xboole_0 @ A @ B ) =
% 1.21/1.39       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.21/1.39  thf('8', plain,
% 1.21/1.39      (![X8 : $i, X9 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X8 @ X9)
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 1.21/1.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.21/1.39  thf('9', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.21/1.39              (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['7', '8'])).
% 1.21/1.39  thf(t49_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i,C:$i]:
% 1.21/1.39     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.21/1.39       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.21/1.39  thf('10', plain,
% 1.21/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.21/1.39           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.21/1.39  thf('11', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.21/1.39              (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1))))),
% 1.21/1.39      inference('demod', [status(thm)], ['9', '10'])).
% 1.21/1.39  thf(t48_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.21/1.39  thf('12', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('13', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('14', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['12', '13'])).
% 1.21/1.39  thf('15', plain,
% 1.21/1.39      (![X12 : $i, X13 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.21/1.39           = (k4_xboole_0 @ X12 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.21/1.39  thf('16', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.21/1.39  thf('17', plain,
% 1.21/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.21/1.39           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.21/1.39  thf(t98_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.21/1.39  thf('18', plain,
% 1.21/1.39      (![X22 : $i, X23 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X22 @ X23)
% 1.21/1.39           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.21/1.39  thf('19', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.21/1.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.21/1.39      inference('sup+', [status(thm)], ['17', '18'])).
% 1.21/1.39  thf('20', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1))
% 1.21/1.39           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['16', '19'])).
% 1.21/1.39  thf('21', plain,
% 1.21/1.39      (![X22 : $i, X23 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X22 @ X23)
% 1.21/1.39           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.21/1.39  thf('22', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('demod', [status(thm)], ['20', '21'])).
% 1.21/1.39  thf('23', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('demod', [status(thm)], ['20', '21'])).
% 1.21/1.39  thf('24', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.21/1.39  thf(t51_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.21/1.39       ( A ) ))).
% 1.21/1.39  thf('25', plain,
% 1.21/1.39      (![X19 : $i, X20 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 1.21/1.39           = (X19))),
% 1.21/1.39      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.21/1.39  thf('26', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.21/1.39           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 1.21/1.39      inference('sup+', [status(thm)], ['24', '25'])).
% 1.21/1.39  thf('27', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('28', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (X1))),
% 1.21/1.39      inference('demod', [status(thm)], ['26', '27'])).
% 1.21/1.39  thf('29', plain,
% 1.21/1.39      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['23', '28'])).
% 1.21/1.39  thf('30', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ 
% 1.21/1.39           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X0 @ X0)) @ 
% 1.21/1.39           X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['22', '29'])).
% 1.21/1.39  thf('31', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf('32', plain,
% 1.21/1.39      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 1.21/1.39           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 1.21/1.39      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.21/1.39  thf('33', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 1.21/1.39           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 1.21/1.39      inference('sup+', [status(thm)], ['31', '32'])).
% 1.21/1.39  thf('34', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('sup+', [status(thm)], ['5', '6'])).
% 1.21/1.39  thf('35', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.21/1.39  thf('36', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 1.21/1.39           = (k3_xboole_0 @ X0 @ X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['30', '33', '34', '35'])).
% 1.21/1.39  thf('37', plain,
% 1.21/1.39      (![X0 : $i]: ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['23', '28'])).
% 1.21/1.39  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['36', '37'])).
% 1.21/1.39  thf('39', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf('40', plain,
% 1.21/1.39      (![X19 : $i, X20 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 1.21/1.39           = (X19))),
% 1.21/1.39      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.21/1.39  thf('41', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 1.21/1.39           = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['39', '40'])).
% 1.21/1.39  thf('42', plain,
% 1.21/1.39      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['38', '41'])).
% 1.21/1.39  thf(l98_xboole_1, axiom,
% 1.21/1.39    (![A:$i,B:$i]:
% 1.21/1.39     ( ( k5_xboole_0 @ A @ B ) =
% 1.21/1.39       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.21/1.39  thf('43', plain,
% 1.21/1.39      (![X10 : $i, X11 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X10 @ X11)
% 1.21/1.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.21/1.39              (k3_xboole_0 @ X10 @ X11)))),
% 1.21/1.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.21/1.39  thf('44', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))))),
% 1.21/1.39      inference('sup+', [status(thm)], ['42', '43'])).
% 1.21/1.39  thf('45', plain,
% 1.21/1.39      (![X22 : $i, X23 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X22 @ X23)
% 1.21/1.39           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 1.21/1.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.21/1.39  thf('46', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.21/1.39  thf('47', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('48', plain,
% 1.21/1.39      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 1.21/1.39  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['36', '37'])).
% 1.21/1.39  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['48', '49'])).
% 1.21/1.39  thf('51', plain,
% 1.21/1.39      (![X8 : $i, X9 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X8 @ X9)
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 1.21/1.39      inference('cnf', [status(esa)], [d6_xboole_0])).
% 1.21/1.39  thf('52', plain,
% 1.21/1.39      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['50', '51'])).
% 1.21/1.39  thf('53', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.21/1.39              (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1))))),
% 1.21/1.39      inference('demod', [status(thm)], ['11', '52'])).
% 1.21/1.39  thf('54', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 1.21/1.39              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['4', '53'])).
% 1.21/1.39  thf('55', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf('56', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (X1))),
% 1.21/1.39      inference('demod', [status(thm)], ['26', '27'])).
% 1.21/1.39  thf('57', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['55', '56'])).
% 1.21/1.39  thf('58', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.21/1.39           = (k1_xboole_0))),
% 1.21/1.39      inference('demod', [status(thm)], ['54', '57'])).
% 1.21/1.39  thf('59', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.21/1.39           = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['3', '58'])).
% 1.21/1.39  thf('60', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.21/1.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.21/1.39      inference('sup+', [status(thm)], ['17', '18'])).
% 1.21/1.39  thf('61', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.21/1.39           = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['59', '60'])).
% 1.21/1.39  thf('62', plain,
% 1.21/1.39      (![X10 : $i, X11 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X10 @ X11)
% 1.21/1.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.21/1.39              (k3_xboole_0 @ X10 @ X11)))),
% 1.21/1.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.21/1.39  thf('63', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ k1_xboole_0 @ 
% 1.21/1.39              (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))))),
% 1.21/1.39      inference('sup+', [status(thm)], ['61', '62'])).
% 1.21/1.39  thf('64', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 1.21/1.39           = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['3', '58'])).
% 1.21/1.39  thf('65', plain,
% 1.21/1.39      (![X12 : $i, X13 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.21/1.39           = (k4_xboole_0 @ X12 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.21/1.39  thf('66', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('67', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['65', '66'])).
% 1.21/1.39  thf('68', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('69', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k3_xboole_0 @ X1 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['67', '68'])).
% 1.21/1.39  thf('70', plain,
% 1.21/1.39      (![X12 : $i, X13 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 1.21/1.39           = (k4_xboole_0 @ X12 @ X13))),
% 1.21/1.39      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.21/1.39  thf('71', plain,
% 1.21/1.39      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['63', '64', '69', '70'])).
% 1.21/1.39  thf('72', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('73', plain,
% 1.21/1.39      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['71', '72'])).
% 1.21/1.39  thf('74', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 1.21/1.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.21/1.39      inference('sup+', [status(thm)], ['17', '18'])).
% 1.21/1.39  thf('75', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 1.21/1.39           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['73', '74'])).
% 1.21/1.39  thf('76', plain,
% 1.21/1.39      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['71', '72'])).
% 1.21/1.39  thf('77', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.21/1.39      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.39  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.21/1.39  thf('79', plain,
% 1.21/1.39      (![X10 : $i, X11 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X10 @ X11)
% 1.21/1.39           = (k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 1.21/1.39              (k3_xboole_0 @ X10 @ X11)))),
% 1.21/1.39      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.21/1.39  thf('80', plain,
% 1.21/1.39      (![X14 : $i, X15 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 1.21/1.39           = (k3_xboole_0 @ X14 @ X15))),
% 1.21/1.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.21/1.39  thf('81', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['79', '80'])).
% 1.21/1.39  thf('82', plain,
% 1.21/1.39      (![X0 : $i]:
% 1.21/1.39         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 1.21/1.39           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.21/1.39              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['78', '81'])).
% 1.21/1.39  thf('83', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 1.21/1.39      inference('cnf', [status(esa)], [t5_boole])).
% 1.21/1.39  thf('84', plain,
% 1.21/1.39      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['50', '51'])).
% 1.21/1.39  thf('85', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.21/1.39  thf('86', plain,
% 1.21/1.39      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['71', '72'])).
% 1.21/1.39  thf('87', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.21/1.39  thf('88', plain,
% 1.21/1.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['86', '87'])).
% 1.21/1.39  thf('89', plain,
% 1.21/1.39      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.21/1.39      inference('demod', [status(thm)], ['82', '83', '84', '85', '88'])).
% 1.21/1.39  thf('90', plain,
% 1.21/1.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['86', '87'])).
% 1.21/1.39  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.21/1.39      inference('demod', [status(thm)], ['89', '90'])).
% 1.21/1.39  thf('92', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.21/1.39              (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X1))))),
% 1.21/1.39      inference('demod', [status(thm)], ['11', '52'])).
% 1.21/1.39  thf('93', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 1.21/1.39              (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 1.21/1.39      inference('sup+', [status(thm)], ['91', '92'])).
% 1.21/1.39  thf('94', plain,
% 1.21/1.39      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.39      inference('sup+', [status(thm)], ['86', '87'])).
% 1.21/1.39  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.21/1.39      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.21/1.39  thf('96', plain,
% 1.21/1.39      (![X0 : $i, X1 : $i]:
% 1.21/1.39         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.21/1.39           = (k4_xboole_0 @ X0 @ X1))),
% 1.21/1.39      inference('demod', [status(thm)], ['93', '94', '95'])).
% 1.21/1.39  thf('97', plain,
% 1.21/1.39      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.21/1.39      inference('demod', [status(thm)], ['2', '96'])).
% 1.21/1.39  thf('98', plain, ($false), inference('simplify', [status(thm)], ['97'])).
% 1.21/1.39  
% 1.21/1.39  % SZS output end Refutation
% 1.21/1.39  
% 1.21/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
