%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gLm73RABOc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:08 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  135 (1012 expanded)
%              Number of leaves         :   20 ( 346 expanded)
%              Depth                    :   22
%              Number of atoms          : 1129 (8264 expanded)
%              Number of equality atoms :  125 (1001 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','26'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('48',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('56',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != ( k4_xboole_0 @ X2 @ X1 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
       != ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X16 ) @ X17 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X17 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('69',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('76',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['74','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('91',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','102'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X3 @ X2 ) )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','111'])).

thf('113',plain,(
    $false ),
    inference(simplify,[status(thm)],['112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gLm73RABOc
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.36/1.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.56  % Solved by: fo/fo7.sh
% 1.36/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.56  % done 1668 iterations in 1.100s
% 1.36/1.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.56  % SZS output start Refutation
% 1.36/1.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.36/1.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.56  thf(t98_xboole_1, conjecture,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.36/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.56    (~( ![A:$i,B:$i]:
% 1.36/1.56        ( ( k2_xboole_0 @ A @ B ) =
% 1.36/1.56          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 1.36/1.56    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 1.36/1.56  thf('0', plain,
% 1.36/1.56      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.36/1.56         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 1.36/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.56  thf(t41_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.36/1.56       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.36/1.56  thf('1', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf(t39_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.36/1.56  thf('2', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.36/1.56           = (k2_xboole_0 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.36/1.56  thf('3', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.36/1.56           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.56  thf(t48_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.36/1.56  thf('4', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.36/1.56           = (k3_xboole_0 @ X10 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.56  thf('5', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf('6', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ X2 @ 
% 1.36/1.56              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 1.36/1.56      inference('sup+', [status(thm)], ['4', '5'])).
% 1.36/1.56  thf('7', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf('8', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ X2 @ 
% 1.36/1.56              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 1.36/1.56      inference('demod', [status(thm)], ['6', '7'])).
% 1.36/1.56  thf('9', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.36/1.56      inference('sup+', [status(thm)], ['3', '8'])).
% 1.36/1.56  thf('10', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.36/1.56           = (k2_xboole_0 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.36/1.56  thf('11', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.36/1.56      inference('demod', [status(thm)], ['9', '10'])).
% 1.36/1.56  thf('12', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf(t3_boole, axiom,
% 1.36/1.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.56  thf('13', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('14', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.36/1.56           = (k3_xboole_0 @ X10 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.56  thf('15', plain,
% 1.36/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['13', '14'])).
% 1.36/1.56  thf('16', plain,
% 1.36/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['13', '14'])).
% 1.36/1.56  thf('17', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf('18', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 1.36/1.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['16', '17'])).
% 1.36/1.56  thf(t46_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.36/1.56  thf('19', plain,
% 1.36/1.56      (![X8 : $i, X9 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 1.36/1.56      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.36/1.56  thf('20', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['18', '19'])).
% 1.36/1.56  thf('21', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('22', plain,
% 1.36/1.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['20', '21'])).
% 1.36/1.56  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['15', '22'])).
% 1.36/1.56  thf('24', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.36/1.56           = (k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['12', '23'])).
% 1.36/1.56  thf('25', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.36/1.56           = (k2_xboole_0 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.36/1.56  thf('26', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['24', '25'])).
% 1.36/1.56  thf('27', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['11', '26'])).
% 1.36/1.56  thf(t94_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( k2_xboole_0 @ A @ B ) =
% 1.36/1.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.36/1.56  thf('28', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.36/1.56              (k3_xboole_0 @ X22 @ X23)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.36/1.56  thf(t91_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.36/1.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.36/1.56  thf('29', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.36/1.56           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.36/1.56  thf('30', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ X22 @ 
% 1.36/1.56              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.36/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.36/1.56  thf('31', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 1.36/1.56              (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['27', '30'])).
% 1.36/1.56  thf(t5_boole, axiom,
% 1.36/1.56    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.56  thf('32', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.56      inference('cnf', [status(esa)], [t5_boole])).
% 1.36/1.56  thf(commutativity_k5_xboole_0, axiom,
% 1.36/1.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.36/1.56  thf('33', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('34', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.36/1.56  thf('35', plain,
% 1.36/1.56      (((k2_xboole_0 @ sk_A @ sk_B)
% 1.36/1.56         != (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ sk_A))),
% 1.36/1.56      inference('demod', [status(thm)], ['0', '34'])).
% 1.36/1.56  thf('36', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('37', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.36/1.56           = (k3_xboole_0 @ X10 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.56  thf('38', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.36/1.56           = (k2_xboole_0 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.36/1.56  thf('39', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.36/1.56      inference('sup+', [status(thm)], ['37', '38'])).
% 1.36/1.56  thf('40', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 1.36/1.56           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['36', '39'])).
% 1.36/1.56  thf('41', plain,
% 1.36/1.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['20', '21'])).
% 1.36/1.56  thf('42', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('43', plain,
% 1.36/1.56      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.36/1.56  thf('44', plain,
% 1.36/1.56      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['20', '21'])).
% 1.36/1.56  thf('45', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ X22 @ 
% 1.36/1.56              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.36/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.36/1.56  thf('46', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['44', '45'])).
% 1.36/1.56  thf('47', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('48', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.56      inference('cnf', [status(esa)], [t5_boole])).
% 1.36/1.56  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['47', '48'])).
% 1.36/1.56  thf('50', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['46', '49'])).
% 1.36/1.56  thf('51', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.56      inference('cnf', [status(esa)], [t5_boole])).
% 1.36/1.56  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['50', '51'])).
% 1.36/1.56  thf('53', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['43', '52'])).
% 1.36/1.56  thf('54', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['43', '52'])).
% 1.36/1.56  thf('55', plain,
% 1.36/1.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 1.36/1.56           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.36/1.56  thf(t83_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i]:
% 1.36/1.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.36/1.56  thf('56', plain,
% 1.36/1.56      (![X13 : $i, X15 : $i]:
% 1.36/1.56         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.36/1.56  thf('57', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.36/1.56            != (k4_xboole_0 @ X2 @ X1))
% 1.36/1.56          | (r1_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.36/1.56      inference('sup-', [status(thm)], ['55', '56'])).
% 1.36/1.56  thf('58', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         (((k4_xboole_0 @ X1 @ X0) != (k4_xboole_0 @ X1 @ X0))
% 1.36/1.56          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.36/1.56      inference('sup-', [status(thm)], ['54', '57'])).
% 1.36/1.56  thf('59', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.36/1.56      inference('simplify', [status(thm)], ['58'])).
% 1.36/1.56  thf(t87_xboole_1, axiom,
% 1.36/1.56    (![A:$i,B:$i,C:$i]:
% 1.36/1.56     ( ( r1_xboole_0 @ A @ B ) =>
% 1.36/1.56       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 1.36/1.56         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 1.36/1.56  thf('60', plain,
% 1.36/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.36/1.56         (~ (r1_xboole_0 @ X16 @ X17)
% 1.36/1.56          | ((k2_xboole_0 @ (k4_xboole_0 @ X18 @ X16) @ X17)
% 1.36/1.56              = (k4_xboole_0 @ (k2_xboole_0 @ X18 @ X17) @ X16)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t87_xboole_1])).
% 1.36/1.56  thf('61', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('sup-', [status(thm)], ['59', '60'])).
% 1.36/1.56  thf('62', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X0)
% 1.36/1.56           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['53', '61'])).
% 1.36/1.56  thf('63', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['24', '25'])).
% 1.36/1.56  thf('64', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.36/1.56           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['1', '2'])).
% 1.36/1.56  thf('65', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.36/1.56           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['63', '64'])).
% 1.36/1.56  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['50', '51'])).
% 1.36/1.56  thf('67', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['65', '66'])).
% 1.36/1.56  thf('68', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ X22 @ 
% 1.36/1.56              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.36/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.36/1.56  thf('69', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.36/1.56           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.36/1.56  thf('70', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('71', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.36/1.56           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['69', '70'])).
% 1.36/1.56  thf('72', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X1 @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['68', '71'])).
% 1.36/1.56  thf('73', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('74', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X1 @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.36/1.56      inference('demod', [status(thm)], ['72', '73'])).
% 1.36/1.56  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['15', '22'])).
% 1.36/1.56  thf('76', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.36/1.56           = (k3_xboole_0 @ X10 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.56  thf('77', plain,
% 1.36/1.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['75', '76'])).
% 1.36/1.56  thf('78', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('79', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['77', '78'])).
% 1.36/1.56  thf('80', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ X22 @ 
% 1.36/1.56              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.36/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.36/1.56  thf('81', plain,
% 1.36/1.56      (![X0 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['79', '80'])).
% 1.36/1.56  thf('82', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['43', '52'])).
% 1.36/1.56  thf('83', plain,
% 1.36/1.56      (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['81', '82'])).
% 1.36/1.56  thf('84', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.36/1.56           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.36/1.56  thf('85', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ X0 @ X1)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['83', '84'])).
% 1.36/1.56  thf('86', plain,
% 1.36/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.36/1.56           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.36/1.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.36/1.56  thf('87', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ X0 @ X1)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1))))),
% 1.36/1.56      inference('demod', [status(thm)], ['85', '86'])).
% 1.36/1.56  thf('88', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.36/1.56      inference('sup+', [status(thm)], ['74', '87'])).
% 1.36/1.56  thf('89', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X1 @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.36/1.56      inference('demod', [status(thm)], ['72', '73'])).
% 1.36/1.56  thf('90', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.36/1.56      inference('demod', [status(thm)], ['24', '25'])).
% 1.36/1.56  thf('91', plain,
% 1.36/1.56      (![X10 : $i, X11 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.36/1.56           = (k3_xboole_0 @ X10 @ X11))),
% 1.36/1.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.36/1.56  thf('92', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.36/1.56           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['90', '91'])).
% 1.36/1.56  thf('93', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.36/1.56      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.56  thf('94', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['92', '93'])).
% 1.36/1.56  thf('95', plain,
% 1.36/1.56      (![X22 : $i, X23 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X22 @ X23)
% 1.36/1.56           = (k5_xboole_0 @ X22 @ 
% 1.36/1.56              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 1.36/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.36/1.56  thf('96', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 1.36/1.56      inference('sup+', [status(thm)], ['94', '95'])).
% 1.36/1.56  thf('97', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('98', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.36/1.56      inference('demod', [status(thm)], ['96', '97'])).
% 1.36/1.56  thf('99', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X1 @ X0)
% 1.36/1.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['88', '89', '98'])).
% 1.36/1.56  thf('100', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.36/1.56           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['67', '99'])).
% 1.36/1.56  thf('101', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['65', '66'])).
% 1.36/1.56  thf('102', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['100', '101'])).
% 1.36/1.56  thf('103', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['62', '102'])).
% 1.36/1.56  thf('104', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.36/1.56  thf('105', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 1.36/1.56           (k4_xboole_0 @ X1 @ X0))
% 1.36/1.56           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.36/1.56      inference('sup+', [status(thm)], ['103', '104'])).
% 1.36/1.56  thf('106', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['62', '102'])).
% 1.36/1.56  thf('107', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.36/1.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.36/1.56  thf('108', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.36/1.56           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.36/1.56      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.36/1.56  thf('109', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.36/1.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 1.36/1.56  thf('110', plain,
% 1.36/1.56      (![X2 : $i, X3 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X3 @ X2))
% 1.36/1.56           = (k2_xboole_0 @ X2 @ X3))),
% 1.36/1.56      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.36/1.56  thf('111', plain,
% 1.36/1.56      (![X0 : $i, X1 : $i]:
% 1.36/1.56         ((k2_xboole_0 @ X0 @ X1)
% 1.36/1.56           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.36/1.56      inference('demod', [status(thm)], ['109', '110'])).
% 1.36/1.56  thf('112', plain,
% 1.36/1.56      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 1.36/1.56      inference('demod', [status(thm)], ['35', '111'])).
% 1.36/1.56  thf('113', plain, ($false), inference('simplify', [status(thm)], ['112'])).
% 1.36/1.56  
% 1.36/1.56  % SZS output end Refutation
% 1.36/1.56  
% 1.36/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
