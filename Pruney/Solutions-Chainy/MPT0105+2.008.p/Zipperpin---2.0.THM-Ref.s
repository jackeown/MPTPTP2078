%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uXuhXR8h73

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:05 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  150 (1965 expanded)
%              Number of leaves         :   20 ( 683 expanded)
%              Depth                    :   32
%              Number of atoms          : 1195 (14774 expanded)
%              Number of equality atoms :  142 (1957 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('50',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','54'])).

thf('56',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['15','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('74',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('76',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70','71','72','73','74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('85',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','88'])).

thf('90',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['0','89'])).

thf('91',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','58'])).

thf('93',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','53'])).

thf('106',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['92','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','58'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('115',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('121',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['91','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','88'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['90','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uXuhXR8h73
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 723 iterations in 0.427s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(t98_xboole_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i]:
% 0.68/0.88        ( ( k2_xboole_0 @ A @ B ) =
% 0.68/0.88          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.68/0.88         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t94_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k2_xboole_0 @ A @ B ) =
% 0.68/0.88       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 0.68/0.88              (k3_xboole_0 @ X23 @ X24)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.68/0.88  thf(t91_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.88       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.68/0.88           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ X23 @ 
% 0.68/0.88              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.68/0.88           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.88  thf(commutativity_k5_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.68/0.88           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ X0)
% 0.68/0.88           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['3', '6'])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf(t47_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.68/0.88  thf(d6_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k5_xboole_0 @ A @ B ) =
% 0.68/0.88       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf(t49_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.88       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['11', '12'])).
% 0.68/0.88  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf(t48_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.68/0.88           = (k3_xboole_0 @ X14 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf(t3_boole, axiom,
% 0.68/0.88    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.88  thf('16', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.68/0.88           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['16', '17'])).
% 0.68/0.88  thf(t5_boole, axiom,
% 0.68/0.88    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.88  thf('19', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.68/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf(t46_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.88  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.68/0.88           = (k3_xboole_0 @ X14 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('25', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('26', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['26', '27'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ X23 @ 
% 0.68/0.88              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k5_xboole_0 @ X1 @ 
% 0.68/0.88              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.88  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ X0)
% 0.68/0.88           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.68/0.88  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['33', '34'])).
% 0.68/0.88  thf('36', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.68/0.88           = (k3_xboole_0 @ X14 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.68/0.88           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['40', '43'])).
% 0.68/0.88  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.68/0.88           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['46', '47'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf('50', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.68/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.88  thf('51', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['49', '50'])).
% 0.68/0.88  thf('52', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('53', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['48', '51', '52'])).
% 0.68/0.88  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '53'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['30', '54'])).
% 0.68/0.88  thf('56', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.68/0.88      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.68/0.88      inference('demod', [status(thm)], ['55', '56'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['15', '57'])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['14', '58'])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.68/0.88           = (k3_xboole_0 @ X14 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['60', '61'])).
% 0.68/0.88  thf(t41_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.88       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.68/0.88           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88              (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88           (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.68/0.88           = (k2_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ 
% 0.68/0.88              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['59', '64'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['49', '50'])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('77', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.88  thf('78', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X1 @ X0)
% 0.68/0.88           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)],
% 0.68/0.88                ['65', '66', '67', '68', '69', '70', '71', '72', '73', '74', 
% 0.68/0.88                 '77'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['78', '79'])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.68/0.88  thf('83', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.68/0.88           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.68/0.88  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '39'])).
% 0.68/0.88  thf('86', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['80', '81', '82', '83', '84', '85'])).
% 0.68/0.88  thf('87', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['75', '76'])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['13', '86', '87'])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ X0)
% 0.68/0.88           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['7', '8', '88'])).
% 0.68/0.88  thf('90', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '89'])).
% 0.68/0.88  thf('91', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ X23 @ 
% 0.68/0.88              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('92', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['14', '58'])).
% 0.68/0.88  thf('93', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.68/0.88           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['80', '81', '82', '83', '84', '85'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      (![X12 : $i, X13 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 0.68/0.88           = (k4_xboole_0 @ X12 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.68/0.88           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['94', '95'])).
% 0.68/0.88  thf('97', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_boole])).
% 0.68/0.88  thf('98', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['96', '97'])).
% 0.68/0.88  thf('99', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((X0)
% 0.68/0.88           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['93', '98'])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.68/0.88           = (k3_xboole_0 @ X14 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['99', '100'])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ X23 @ 
% 0.68/0.88              (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X23 @ X24))))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('103', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['101', '102'])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('demod', [status(thm)], ['35', '53'])).
% 0.68/0.88  thf('106', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.68/0.88           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.68/0.88  thf('107', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.68/0.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['105', '106'])).
% 0.68/0.88  thf('108', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['49', '50'])).
% 0.68/0.88  thf('109', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['107', '108'])).
% 0.68/0.88  thf('110', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['103', '104', '109'])).
% 0.68/0.88  thf('111', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.68/0.88           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['92', '110'])).
% 0.68/0.88  thf('112', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['14', '58'])).
% 0.68/0.88  thf('113', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['111', '112'])).
% 0.68/0.88  thf('114', plain,
% 0.68/0.88      (![X10 : $i, X11 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.68/0.88      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.68/0.88  thf('115', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X4 @ X5)
% 0.68/0.88           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.68/0.88  thf('116', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.68/0.88              (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['114', '115'])).
% 0.68/0.88  thf('117', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['48', '51', '52'])).
% 0.68/0.88  thf('118', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.68/0.88           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['116', '117'])).
% 0.68/0.88  thf('119', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.68/0.88           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['113', '118'])).
% 0.68/0.88  thf('120', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['111', '112'])).
% 0.68/0.88  thf('121', plain,
% 0.68/0.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.68/0.88  thf('122', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['41', '42'])).
% 0.68/0.88  thf('123', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.88           = (k4_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.68/0.88  thf('124', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X23 @ X24)
% 0.68/0.88           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.68/0.88      inference('demod', [status(thm)], ['91', '123'])).
% 0.68/0.88  thf('125', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X1 @ X0)
% 0.68/0.88           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['7', '8', '88'])).
% 0.68/0.88  thf('126', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['124', '125'])).
% 0.68/0.88  thf('127', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['90', '126'])).
% 0.68/0.88  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
