%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VbXp2rdrYu

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:07 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 226 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  656 (1813 expanded)
%              Number of equality atoms :   75 ( 218 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X30 @ X31 ) @ ( k3_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k5_xboole_0 @ X31 @ ( k3_xboole_0 @ X30 @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ X3 @ X4 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X27 @ X28 ) @ X29 )
      = ( k5_xboole_0 @ X27 @ ( k5_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16','29'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ X3 @ X4 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('56',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['37','57','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VbXp2rdrYu
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 635 iterations in 0.311s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.76  thf(t98_xboole_1, conjecture,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i,B:$i]:
% 0.59/0.76        ( ( k2_xboole_0 @ A @ B ) =
% 0.59/0.76          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.59/0.76         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.76  thf('1', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.59/0.76      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.76  thf(t46_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (![X13 : $i, X14 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.59/0.76      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.76  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.76  thf(t41_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.76       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.76           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k1_xboole_0)
% 0.59/0.76           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.59/0.76      inference('sup+', [status(thm)], ['3', '4'])).
% 0.59/0.76  thf(t39_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('6', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.59/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.76  thf(t48_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('9', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.59/0.76           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.76  thf(t3_boole, axiom,
% 0.59/0.76    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.76  thf('10', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.76  thf(t94_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k2_xboole_0 @ A @ B ) =
% 0.59/0.76       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      (![X30 : $i, X31 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X30 @ X31)
% 0.59/0.76           = (k5_xboole_0 @ (k5_xboole_0 @ X30 @ X31) @ 
% 0.59/0.76              (k3_xboole_0 @ X30 @ X31)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.59/0.76  thf(t91_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.76       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.76  thf('13', plain,
% 0.59/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.59/0.76           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.76  thf('14', plain,
% 0.59/0.76      (![X30 : $i, X31 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X30 @ X31)
% 0.59/0.76           = (k5_xboole_0 @ X30 @ 
% 0.59/0.76              (k5_xboole_0 @ X31 @ (k3_xboole_0 @ X30 @ X31))))),
% 0.59/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.59/0.76  thf('15', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.76           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['11', '14'])).
% 0.59/0.76  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.76  thf('16', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.76  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.59/0.76      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.76  thf(l98_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k5_xboole_0 @ A @ B ) =
% 0.59/0.76       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.76  thf('18', plain,
% 0.59/0.76      (![X3 : $i, X4 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ X3 @ X4)
% 0.59/0.76           = (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.59/0.76      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.59/0.76  thf('19', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ X0 @ X0)
% 0.59/0.76           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['17', '18'])).
% 0.59/0.76  thf(t47_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('20', plain,
% 0.59/0.76      (![X15 : $i, X16 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.59/0.76           = (k4_xboole_0 @ X15 @ X16))),
% 0.59/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.59/0.76  thf('21', plain,
% 0.59/0.76      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.76  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.76  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.76  thf('24', plain,
% 0.59/0.76      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X27 @ X28) @ X29)
% 0.59/0.76           = (k5_xboole_0 @ X27 @ (k5_xboole_0 @ X28 @ X29)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.76  thf('25', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.76           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.76  thf('26', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.76  thf(t5_boole, axiom,
% 0.59/0.76    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.76  thf('27', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.76  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['26', '27'])).
% 0.59/0.76  thf('29', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('demod', [status(thm)], ['25', '28'])).
% 0.59/0.76  thf('30', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.76           = (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.76      inference('demod', [status(thm)], ['15', '16', '29'])).
% 0.59/0.76  thf(t40_xboole_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]:
% 0.59/0.76     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.76  thf('31', plain,
% 0.59/0.76      (![X8 : $i, X9 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 0.59/0.76           = (k4_xboole_0 @ X8 @ X9))),
% 0.59/0.76      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.76  thf('32', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('33', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.76           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['31', '32'])).
% 0.59/0.76  thf('34', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('35', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.59/0.76           = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('sup+', [status(thm)], ['33', '34'])).
% 0.59/0.76  thf('36', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('sup+', [status(thm)], ['30', '35'])).
% 0.59/0.76  thf('37', plain,
% 0.59/0.76      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.59/0.76         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['0', '36'])).
% 0.59/0.76  thf('38', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.76           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.76  thf('39', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.59/0.76           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.76  thf('41', plain,
% 0.59/0.76      (![X17 : $i, X18 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.76  thf('42', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.76           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.76  thf('43', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.59/0.76           = (k4_xboole_0 @ X2 @ 
% 0.59/0.76              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.59/0.76      inference('sup+', [status(thm)], ['41', '42'])).
% 0.59/0.76  thf('44', plain,
% 0.59/0.76      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.76         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.59/0.76           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.59/0.76      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.76  thf('45', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.59/0.76           = (k4_xboole_0 @ X2 @ 
% 0.59/0.76              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.59/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.76  thf('46', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.76           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.59/0.76      inference('sup+', [status(thm)], ['40', '45'])).
% 0.59/0.76  thf('47', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('48', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.76           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.59/0.76      inference('demod', [status(thm)], ['46', '47'])).
% 0.59/0.76  thf('49', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.59/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.76  thf('50', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.59/0.76      inference('demod', [status(thm)], ['48', '49'])).
% 0.59/0.76  thf('51', plain,
% 0.59/0.76      (![X3 : $i, X4 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ X3 @ X4)
% 0.59/0.76           = (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ (k3_xboole_0 @ X3 @ X4)))),
% 0.59/0.76      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.76           = (k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ 
% 0.59/0.76              k1_xboole_0))),
% 0.59/0.76      inference('sup+', [status(thm)], ['50', '51'])).
% 0.59/0.76  thf('53', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.76  thf('54', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('sup+', [status(thm)], ['30', '35'])).
% 0.59/0.76  thf('55', plain,
% 0.59/0.76      (![X5 : $i, X6 : $i]:
% 0.59/0.76         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.59/0.76           = (k2_xboole_0 @ X5 @ X6))),
% 0.59/0.76      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.76  thf('56', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.76  thf('57', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.76           = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.59/0.76  thf('58', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.76      inference('sup+', [status(thm)], ['30', '35'])).
% 0.59/0.76  thf('59', plain,
% 0.59/0.76      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.76      inference('demod', [status(thm)], ['37', '57', '58'])).
% 0.59/0.76  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.59/0.76  
% 0.59/0.76  % SZS output end Refutation
% 0.59/0.76  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
