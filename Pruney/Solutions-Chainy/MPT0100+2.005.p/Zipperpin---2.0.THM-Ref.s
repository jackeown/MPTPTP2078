%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WGAlS5ngfQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:53 EST 2020

% Result     : Theorem 44.73s
% Output     : Refutation 44.73s
% Verified   : 
% Statistics : Number of formulae       :  256 (7377 expanded)
%              Number of leaves         :   18 (2593 expanded)
%              Depth                    :   31
%              Number of atoms          : 2311 (57710 expanded)
%              Number of equality atoms :  248 (7369 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t93_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = X2 ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = X2 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = X2 ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('68',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['50','51','52','60','65','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','87'])).

thf('89',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('90',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['88','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','93'])).

thf('95',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['20','98','99'])).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('102',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('106',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('107',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('125',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('127',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','130'])).

thf('132',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('134',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['133','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','130'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('140',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126','129'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['138','144'])).

thf('146',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('147',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['137','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','147'])).

thf('149',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','80'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('154',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['152','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('160',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('166',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['164','172'])).

thf('174',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['158','173','174'])).

thf('176',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['149','179'])).

thf('181',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['148','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('185',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['183','192'])).

thf('194',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('195',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['202','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X1 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['193','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('209',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('211',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('212',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('224',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['222','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['104','113','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','234'])).

thf('236',plain,(
    $false ),
    inference(simplify,[status(thm)],['235'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WGAlS5ngfQ
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 44.73/45.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.73/45.02  % Solved by: fo/fo7.sh
% 44.73/45.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.73/45.02  % done 15749 iterations in 44.558s
% 44.73/45.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.73/45.02  % SZS output start Refutation
% 44.73/45.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.73/45.02  thf(sk_A_type, type, sk_A: $i).
% 44.73/45.02  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 44.73/45.02  thf(sk_B_type, type, sk_B: $i).
% 44.73/45.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.73/45.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.73/45.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.73/45.02  thf(t93_xboole_1, conjecture,
% 44.73/45.02    (![A:$i,B:$i]:
% 44.73/45.02     ( ( k2_xboole_0 @ A @ B ) =
% 44.73/45.02       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 44.73/45.02  thf(zf_stmt_0, negated_conjecture,
% 44.73/45.02    (~( ![A:$i,B:$i]:
% 44.73/45.02        ( ( k2_xboole_0 @ A @ B ) =
% 44.73/45.02          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 44.73/45.02    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 44.73/45.02  thf('0', plain,
% 44.73/45.02      (((k2_xboole_0 @ sk_A @ sk_B)
% 44.73/45.02         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 44.73/45.02             (k3_xboole_0 @ sk_A @ sk_B)))),
% 44.73/45.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.73/45.02  thf(d6_xboole_0, axiom,
% 44.73/45.02    (![A:$i,B:$i]:
% 44.73/45.02     ( ( k5_xboole_0 @ A @ B ) =
% 44.73/45.02       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 44.73/45.02  thf('1', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf(t48_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i]:
% 44.73/45.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 44.73/45.02  thf('2', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf(t41_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i,C:$i]:
% 44.73/45.02     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 44.73/45.02       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 44.73/45.02  thf('3', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('4', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['2', '3'])).
% 44.73/45.02  thf('5', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf(t51_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i]:
% 44.73/45.02     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 44.73/45.02       ( A ) ))).
% 44.73/45.02  thf('6', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('7', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 44.73/45.02           (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['5', '6'])).
% 44.73/45.02  thf(commutativity_k2_xboole_0, axiom,
% 44.73/45.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 44.73/45.02  thf('8', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('9', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/45.02  thf('10', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ 
% 44.73/45.02           (k3_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)) @ 
% 44.73/45.02           (k3_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))
% 44.73/45.02           = (X2))),
% 44.73/45.02      inference('sup+', [status(thm)], ['4', '9'])).
% 44.73/45.02  thf('11', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('12', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ 
% 44.73/45.02           (k3_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)) @ 
% 44.73/45.02           (k3_xboole_0 @ X2 @ (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 44.73/45.02           = (X2))),
% 44.73/45.02      inference('demod', [status(thm)], ['10', '11'])).
% 44.73/45.02  thf('13', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf(t52_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i,C:$i]:
% 44.73/45.02     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 44.73/45.02       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 44.73/45.02  thf('14', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('15', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 44.73/45.02           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['13', '14'])).
% 44.73/45.02  thf('16', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('17', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('18', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 44.73/45.02           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)))),
% 44.73/45.02      inference('demod', [status(thm)], ['15', '16', '17'])).
% 44.73/45.02  thf('19', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ X2 @ 
% 44.73/45.02           (k2_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 44.73/45.02            (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 44.73/45.02           = (X2))),
% 44.73/45.02      inference('demod', [status(thm)], ['12', '18'])).
% 44.73/45.02  thf('20', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ X1 @ 
% 44.73/45.02           (k2_xboole_0 @ 
% 44.73/45.02            (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)) @ 
% 44.73/45.02            (k5_xboole_0 @ X1 @ X0)))
% 44.73/45.02           = (X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['1', '19'])).
% 44.73/45.02  thf('21', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('22', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['2', '3'])).
% 44.73/45.02  thf('23', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['21', '22'])).
% 44.73/45.02  thf('24', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('25', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('26', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k5_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['24', '25'])).
% 44.73/45.02  thf('27', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('28', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['26', '27'])).
% 44.73/45.02  thf('29', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('30', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('31', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf(t40_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i]:
% 44.73/45.02     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 44.73/45.02  thf('32', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('33', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 44.73/45.02           = (k4_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['31', '32'])).
% 44.73/45.02  thf('34', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 44.73/45.02           (k4_xboole_0 @ X2 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['30', '33'])).
% 44.73/45.02  thf('35', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('36', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X2 @ 
% 44.73/45.02           (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X1)))
% 44.73/45.02           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1)))),
% 44.73/45.02      inference('demod', [status(thm)], ['34', '35'])).
% 44.73/45.02  thf('37', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['29', '36'])).
% 44.73/45.02  thf(commutativity_k3_xboole_0, axiom,
% 44.73/45.02    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 44.73/45.02  thf('38', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf(t3_boole, axiom,
% 44.73/45.02    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 44.73/45.02  thf('39', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('40', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('41', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['39', '40'])).
% 44.73/45.02  thf('42', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('43', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/45.02  thf('44', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('45', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('46', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['44', '45'])).
% 44.73/45.02  thf('47', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('48', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('49', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 44.73/45.02           = (k2_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['46', '47', '48'])).
% 44.73/45.02  thf('50', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ 
% 44.73/45.02           (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 44.73/45.02           (k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))
% 44.73/45.02           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['43', '49'])).
% 44.73/45.02  thf('51', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('52', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('53', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('54', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('55', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['53', '54'])).
% 44.73/45.02  thf('56', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('57', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X0 @ X0)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 44.73/45.02              (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['55', '56'])).
% 44.73/45.02  thf('58', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('59', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('60', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['57', '58', '59'])).
% 44.73/45.02  thf('61', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['53', '54'])).
% 44.73/45.02  thf('62', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('63', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['61', '62'])).
% 44.73/45.02  thf('64', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['57', '58', '59'])).
% 44.73/45.02  thf('65', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['63', '64'])).
% 44.73/45.02  thf('66', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('67', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('68', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('69', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['67', '68'])).
% 44.73/45.02  thf('70', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('71', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['69', '70'])).
% 44.73/45.02  thf('72', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['71', '72'])).
% 44.73/45.02  thf('74', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('75', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['73', '74'])).
% 44.73/45.02  thf('76', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['57', '58', '59'])).
% 44.73/45.02  thf('77', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['75', '76'])).
% 44.73/45.02  thf('78', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['53', '54'])).
% 44.73/45.02  thf('79', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['57', '58', '59'])).
% 44.73/45.02  thf('80', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['78', '79'])).
% 44.73/45.02  thf('81', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['77', '80'])).
% 44.73/45.02  thf('82', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['66', '81'])).
% 44.73/45.02  thf('83', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['77', '80'])).
% 44.73/45.02  thf('84', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('85', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['82', '83', '84'])).
% 44.73/45.02  thf('86', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/45.02  thf('87', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)],
% 44.73/45.02                ['50', '51', '52', '60', '65', '85', '86'])).
% 44.73/45.02  thf('88', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['38', '87'])).
% 44.73/45.02  thf('89', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('90', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('91', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['89', '90'])).
% 44.73/45.02  thf('92', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('93', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['88', '91', '92'])).
% 44.73/45.02  thf('94', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('demod', [status(thm)], ['37', '93'])).
% 44.73/45.02  thf('95', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('96', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k3_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['94', '95'])).
% 44.73/45.02  thf('97', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k3_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['28', '96'])).
% 44.73/45.02  thf('98', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k3_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['23', '97'])).
% 44.73/45.02  thf('99', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('100', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ X1 @ 
% 44.73/45.02           (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))
% 44.73/45.02           = (X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['20', '98', '99'])).
% 44.73/45.02  thf('101', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('102', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('103', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['101', '102'])).
% 44.73/45.02  thf('104', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ 
% 44.73/45.02           (k4_xboole_0 @ 
% 44.73/45.02            (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)) @ 
% 44.73/45.02            X0))
% 44.73/45.02           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['100', '103'])).
% 44.73/45.02  thf('105', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/45.02  thf('106', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('107', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('108', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 44.73/45.02           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['106', '107'])).
% 44.73/45.02  thf('109', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('110', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))
% 44.73/45.02           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 44.73/45.02      inference('demod', [status(thm)], ['108', '109'])).
% 44.73/45.02  thf('111', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X2 @ 
% 44.73/45.02           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 44.73/45.02            (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))
% 44.73/45.02           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['105', '110'])).
% 44.73/45.02  thf('112', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/45.02  thf('113', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X2 @ X0)
% 44.73/45.02           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['111', '112'])).
% 44.73/45.02  thf('114', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['26', '27'])).
% 44.73/45.02  thf('115', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k5_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['24', '25'])).
% 44.73/45.02  thf('116', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 44.73/45.02           = (k4_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['31', '32'])).
% 44.73/45.02  thf('117', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['115', '116'])).
% 44.73/45.02  thf('118', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('119', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 44.73/45.02      inference('demod', [status(thm)], ['117', '118'])).
% 44.73/45.02  thf('120', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['63', '64'])).
% 44.73/45.02  thf('121', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['82', '83', '84'])).
% 44.73/45.02  thf('122', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['7', '8'])).
% 44.73/45.02  thf('123', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ k1_xboole_0 @ 
% 44.73/45.02            (k4_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))))
% 44.73/45.02           = (k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['121', '122'])).
% 44.73/45.02  thf('124', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['77', '80'])).
% 44.73/45.02  thf('125', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('126', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['82', '83', '84'])).
% 44.73/45.02  thf('127', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('128', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['41', '42'])).
% 44.73/45.02  thf('129', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['127', '128'])).
% 44.73/45.02  thf('130', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['123', '124', '125', '126', '129'])).
% 44.73/45.02  thf('131', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['120', '130'])).
% 44.73/45.02  thf('132', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('133', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['131', '132'])).
% 44.73/45.02  thf(l36_xboole_1, axiom,
% 44.73/45.02    (![A:$i,B:$i,C:$i]:
% 44.73/45.02     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 44.73/45.02       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 44.73/45.02  thf('134', plain,
% 44.73/45.02      (![X6 : $i, X7 : $i, X8 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X8)))),
% 44.73/45.02      inference('cnf', [status(esa)], [l36_xboole_1])).
% 44.73/45.02  thf('135', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('136', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['134', '135'])).
% 44.73/45.02  thf('137', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))
% 44.73/45.02           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1))))),
% 44.73/45.02      inference('sup+', [status(thm)], ['133', '136'])).
% 44.73/45.02  thf('138', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['120', '130'])).
% 44.73/45.02  thf('139', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['77', '80'])).
% 44.73/45.02  thf('140', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('141', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 44.73/45.02           (k3_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['139', '140'])).
% 44.73/45.02  thf('142', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['123', '124', '125', '126', '129'])).
% 44.73/45.02  thf('143', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['71', '72'])).
% 44.73/45.02  thf('144', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['141', '142', '143'])).
% 44.73/45.02  thf('145', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['138', '144'])).
% 44.73/45.02  thf('146', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('147', plain,
% 44.73/45.02      (![X0 : $i, X2 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['137', '145', '146'])).
% 44.73/45.02  thf('148', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['119', '147'])).
% 44.73/45.02  thf('149', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('150', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['77', '80'])).
% 44.73/45.02  thf('151', plain,
% 44.73/45.02      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['141', '142', '143'])).
% 44.73/45.02  thf('152', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['150', '151'])).
% 44.73/45.02  thf('153', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('154', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('155', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['153', '154'])).
% 44.73/45.02  thf('156', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('157', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 44.73/45.02      inference('demod', [status(thm)], ['155', '156'])).
% 44.73/45.02  thf('158', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['152', '157'])).
% 44.73/45.02  thf('159', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['75', '76'])).
% 44.73/45.02  thf('160', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('161', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ 
% 44.73/45.02              (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['159', '160'])).
% 44.73/45.02  thf('162', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('163', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('164', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['161', '162', '163'])).
% 44.73/45.02  thf('165', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['53', '54'])).
% 44.73/45.02  thf('166', plain,
% 44.73/45.02      (![X17 : $i, X18 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 44.73/45.02           = (X17))),
% 44.73/45.02      inference('cnf', [status(esa)], [t51_xboole_1])).
% 44.73/45.02  thf('167', plain,
% 44.73/45.02      (![X0 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['165', '166'])).
% 44.73/45.02  thf('168', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('169', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('170', plain,
% 44.73/45.02      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['167', '168', '169'])).
% 44.73/45.02  thf('171', plain,
% 44.73/45.02      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['57', '58', '59'])).
% 44.73/45.02  thf('172', plain,
% 44.73/45.02      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['170', '171'])).
% 44.73/45.02  thf('173', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['164', '172'])).
% 44.73/45.02  thf('174', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('175', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['158', '173', '174'])).
% 44.73/45.02  thf('176', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('177', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['175', '176'])).
% 44.73/45.02  thf('178', plain,
% 44.73/45.02      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.73/45.02      inference('demod', [status(thm)], ['150', '151'])).
% 44.73/45.02  thf('179', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['177', '178'])).
% 44.73/45.02  thf('180', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 44.73/45.02              (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.73/45.02      inference('sup+', [status(thm)], ['149', '179'])).
% 44.73/45.02  thf('181', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('182', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ X2 @ 
% 44.73/45.02              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 44.73/45.02      inference('demod', [status(thm)], ['180', '181'])).
% 44.73/45.02  thf('183', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 44.73/45.02      inference('sup+', [status(thm)], ['148', '182'])).
% 44.73/45.02  thf('184', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['177', '178'])).
% 44.73/45.02  thf('185', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('186', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 44.73/45.02           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['184', '185'])).
% 44.73/45.02  thf('187', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('188', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['186', '187'])).
% 44.73/45.02  thf('189', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['101', '102'])).
% 44.73/45.02  thf('190', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 44.73/45.02           = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['188', '189'])).
% 44.73/45.02  thf('191', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 44.73/45.02           = (k4_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['31', '32'])).
% 44.73/45.02  thf('192', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['190', '191'])).
% 44.73/45.02  thf('193', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('demod', [status(thm)], ['183', '192'])).
% 44.73/45.02  thf('194', plain,
% 44.73/45.02      (![X10 : $i, X11 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 44.73/45.02           = (k4_xboole_0 @ X10 @ X11))),
% 44.73/45.02      inference('cnf', [status(esa)], [t40_xboole_1])).
% 44.73/45.02  thf('195', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('196', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['194', '195'])).
% 44.73/45.02  thf('197', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('198', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['196', '197'])).
% 44.73/45.02  thf('199', plain,
% 44.73/45.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 44.73/45.02              (k3_xboole_0 @ X19 @ X21)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t52_xboole_1])).
% 44.73/45.02  thf('200', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 44.73/45.02           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 44.73/45.02              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['198', '199'])).
% 44.73/45.02  thf('201', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('202', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 44.73/45.02           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 44.73/45.02              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)))),
% 44.73/45.02      inference('demod', [status(thm)], ['200', '201'])).
% 44.73/45.02  thf('203', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('204', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['186', '187'])).
% 44.73/45.02  thf('205', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['203', '204'])).
% 44.73/45.02  thf('206', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 44.73/45.02           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 44.73/45.02           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)))),
% 44.73/45.02      inference('demod', [status(thm)], ['202', '205'])).
% 44.73/45.02  thf('207', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X1) @ 
% 44.73/45.02           k1_xboole_0)
% 44.73/45.02           = (k2_xboole_0 @ X1 @ 
% 44.73/45.02              (k3_xboole_0 @ (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X1) @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['193', '206'])).
% 44.73/45.02  thf('208', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('209', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('210', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 44.73/45.02  thf('211', plain,
% 44.73/45.02      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 44.73/45.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 44.73/45.02  thf('212', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('213', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['177', '178'])).
% 44.73/45.02  thf('214', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['212', '213'])).
% 44.73/45.02  thf('215', plain,
% 44.73/45.02      (![X12 : $i, X13 : $i, X14 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 44.73/45.02           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 44.73/45.02      inference('cnf', [status(esa)], [t41_xboole_1])).
% 44.73/45.02  thf('216', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0)
% 44.73/45.02           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 44.73/45.02      inference('demod', [status(thm)], ['214', '215'])).
% 44.73/45.02  thf('217', plain,
% 44.73/45.02      (![X15 : $i, X16 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 44.73/45.02           = (k3_xboole_0 @ X15 @ X16))),
% 44.73/45.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.73/45.02  thf('218', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 44.73/45.02           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 44.73/45.02      inference('sup+', [status(thm)], ['216', '217'])).
% 44.73/45.02  thf('219', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 44.73/45.02      inference('cnf', [status(esa)], [t3_boole])).
% 44.73/45.02  thf('220', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((X1)
% 44.73/45.02           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 44.73/45.02      inference('demod', [status(thm)], ['218', '219'])).
% 44.73/45.02  thf('221', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k2_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)],
% 44.73/45.02                ['207', '208', '209', '210', '211', '220'])).
% 44.73/45.02  thf('222', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k2_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['114', '221'])).
% 44.73/45.02  thf('223', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 44.73/45.02      inference('demod', [status(thm)], ['177', '178'])).
% 44.73/45.02  thf('224', plain,
% 44.73/45.02      (![X4 : $i, X5 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X4 @ X5)
% 44.73/45.02           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 44.73/45.02      inference('cnf', [status(esa)], [d6_xboole_0])).
% 44.73/45.02  thf('225', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k2_xboole_0 @ k1_xboole_0 @ 
% 44.73/45.02              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 44.73/45.02      inference('sup+', [status(thm)], ['223', '224'])).
% 44.73/45.02  thf('226', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 44.73/45.02           = (k4_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['31', '32'])).
% 44.73/45.02  thf('227', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.73/45.02      inference('sup+', [status(thm)], ['71', '72'])).
% 44.73/45.02  thf('228', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['225', '226', '227'])).
% 44.73/45.02  thf('229', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 44.73/45.02      inference('sup+', [status(thm)], ['222', '228'])).
% 44.73/45.02  thf('230', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 44.73/45.02           = (k4_xboole_0 @ X1 @ X0))),
% 44.73/45.02      inference('demod', [status(thm)], ['225', '226', '227'])).
% 44.73/45.02  thf('231', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k4_xboole_0 @ X0 @ X1)
% 44.73/45.02           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['229', '230'])).
% 44.73/45.02  thf('232', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('demod', [status(thm)], ['104', '113', '231'])).
% 44.73/45.02  thf('233', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 44.73/45.02           = (k2_xboole_0 @ X0 @ X1))),
% 44.73/45.02      inference('demod', [status(thm)], ['190', '191'])).
% 44.73/45.02  thf('234', plain,
% 44.73/45.02      (![X0 : $i, X1 : $i]:
% 44.73/45.02         ((k2_xboole_0 @ X0 @ X1)
% 44.73/45.02           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 44.73/45.02      inference('demod', [status(thm)], ['232', '233'])).
% 44.73/45.02  thf('235', plain,
% 44.73/45.02      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 44.73/45.02      inference('demod', [status(thm)], ['0', '234'])).
% 44.73/45.02  thf('236', plain, ($false), inference('simplify', [status(thm)], ['235'])).
% 44.73/45.02  
% 44.73/45.02  % SZS output end Refutation
% 44.73/45.02  
% 44.73/45.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
