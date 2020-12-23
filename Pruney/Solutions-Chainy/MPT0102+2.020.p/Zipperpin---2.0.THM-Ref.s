%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBHuwXcztU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:00 EST 2020

% Result     : Theorem 49.45s
% Output     : Refutation 49.45s
% Verified   : 
% Statistics : Number of formulae       :  191 (1672 expanded)
%              Number of leaves         :   18 ( 571 expanded)
%              Depth                    :   26
%              Number of atoms          : 1668 (11763 expanded)
%              Number of equality atoms :  183 (1664 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','42'])).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','47'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['59','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','47'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('95',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','103'])).

thf('105',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','112','113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('120',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('124',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['117','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('129',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('133',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('138',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','139'])).

thf('141',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','41'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','143'])).

thf('145',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('146',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','41'])).

thf('150',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('151',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('160',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['126','127','128','148','157','158','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','167'])).

thf('169',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('170',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','168','169'])).

thf('171',plain,(
    $false ),
    inference(simplify,[status(thm)],['170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eBHuwXcztU
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 49.45/49.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 49.45/49.63  % Solved by: fo/fo7.sh
% 49.45/49.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.45/49.63  % done 15728 iterations in 49.172s
% 49.45/49.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 49.45/49.63  % SZS output start Refutation
% 49.45/49.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 49.45/49.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 49.45/49.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 49.45/49.63  thf(sk_A_type, type, sk_A: $i).
% 49.45/49.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 49.45/49.63  thf(sk_B_type, type, sk_B: $i).
% 49.45/49.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 49.45/49.63  thf(t95_xboole_1, conjecture,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k3_xboole_0 @ A @ B ) =
% 49.45/49.63       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 49.45/49.63  thf(zf_stmt_0, negated_conjecture,
% 49.45/49.63    (~( ![A:$i,B:$i]:
% 49.45/49.63        ( ( k3_xboole_0 @ A @ B ) =
% 49.45/49.63          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 49.45/49.63    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 49.45/49.63  thf('0', plain,
% 49.45/49.63      (((k3_xboole_0 @ sk_A @ sk_B)
% 49.45/49.63         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 49.45/49.63             (k2_xboole_0 @ sk_A @ sk_B)))),
% 49.45/49.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.45/49.63  thf(d6_xboole_0, axiom,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k5_xboole_0 @ A @ B ) =
% 49.45/49.63       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 49.45/49.63  thf('1', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf(commutativity_k2_xboole_0, axiom,
% 49.45/49.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 49.45/49.63  thf('2', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('3', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['1', '2'])).
% 49.45/49.63  thf('4', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('5', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['3', '4'])).
% 49.45/49.63  thf('6', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['1', '2'])).
% 49.45/49.63  thf('7', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf(t40_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 49.45/49.63  thf('8', plain,
% 49.45/49.63      (![X9 : $i, X10 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 49.45/49.63           = (k4_xboole_0 @ X9 @ X10))),
% 49.45/49.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 49.45/49.63  thf('9', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 49.45/49.63           = (k4_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['7', '8'])).
% 49.45/49.63  thf('10', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['6', '9'])).
% 49.45/49.63  thf(t41_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i,C:$i]:
% 49.45/49.63     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 49.45/49.63       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 49.45/49.63  thf('11', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('12', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))))),
% 49.45/49.63      inference('demod', [status(thm)], ['10', '11'])).
% 49.45/49.63  thf(t51_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 49.45/49.63       ( A ) ))).
% 49.45/49.63  thf('13', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('14', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('15', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf(t1_boole, axiom,
% 49.45/49.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 49.45/49.63  thf('16', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 49.45/49.63      inference('cnf', [status(esa)], [t1_boole])).
% 49.45/49.63  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf(t22_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 49.45/49.63  thf('18', plain,
% 49.45/49.63      (![X7 : $i, X8 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 49.45/49.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 49.45/49.63  thf('19', plain,
% 49.45/49.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['17', '18'])).
% 49.45/49.63  thf(commutativity_k3_xboole_0, axiom,
% 49.45/49.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 49.45/49.63  thf('20', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('21', plain,
% 49.45/49.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['19', '20'])).
% 49.45/49.63  thf('22', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('23', plain,
% 49.45/49.63      (![X0 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['21', '22'])).
% 49.45/49.63  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['23', '24'])).
% 49.45/49.63  thf(t48_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 49.45/49.63  thf('26', plain,
% 49.45/49.63      (![X16 : $i, X17 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 49.45/49.63           = (k3_xboole_0 @ X16 @ X17))),
% 49.45/49.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.45/49.63  thf('27', plain,
% 49.45/49.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['25', '26'])).
% 49.45/49.63  thf('28', plain,
% 49.45/49.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['19', '20'])).
% 49.45/49.63  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['27', '28'])).
% 49.45/49.63  thf('30', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('31', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 49.45/49.63           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['29', '30'])).
% 49.45/49.63  thf('32', plain,
% 49.45/49.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['17', '18'])).
% 49.45/49.63  thf('33', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('34', plain,
% 49.45/49.63      (![X0 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 49.45/49.63           = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['32', '33'])).
% 49.45/49.63  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('36', plain,
% 49.45/49.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['34', '35'])).
% 49.45/49.63  thf('37', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['31', '36'])).
% 49.45/49.63  thf('38', plain,
% 49.45/49.63      (![X16 : $i, X17 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 49.45/49.63           = (k3_xboole_0 @ X16 @ X17))),
% 49.45/49.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.45/49.63  thf('39', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 49.45/49.63           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['37', '38'])).
% 49.45/49.63  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['23', '24'])).
% 49.45/49.63  thf('41', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['39', '40'])).
% 49.45/49.63  thf('42', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['14', '41'])).
% 49.45/49.63  thf('43', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['13', '42'])).
% 49.45/49.63  thf('44', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('45', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['43', '44'])).
% 49.45/49.63  thf('46', plain,
% 49.45/49.63      (![X7 : $i, X8 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 49.45/49.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 49.45/49.63  thf('47', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['45', '46'])).
% 49.45/49.63  thf('48', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['12', '47'])).
% 49.45/49.63  thf(t47_xboole_1, axiom,
% 49.45/49.63    (![A:$i,B:$i]:
% 49.45/49.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 49.45/49.63  thf('49', plain,
% 49.45/49.63      (![X14 : $i, X15 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 49.45/49.63           = (k4_xboole_0 @ X14 @ X15))),
% 49.45/49.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 49.45/49.63  thf('50', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('51', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 49.45/49.63           (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['49', '50'])).
% 49.45/49.63  thf('52', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('53', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63           (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))) = (X1))),
% 49.45/49.63      inference('demod', [status(thm)], ['51', '52'])).
% 49.45/49.63  thf('54', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('55', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('56', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 49.45/49.63           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 49.45/49.63           = (k4_xboole_0 @ X2 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['54', '55'])).
% 49.45/49.63  thf('57', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ 
% 49.45/49.63           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 49.45/49.63            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))) @ 
% 49.45/49.63           (k4_xboole_0 @ X2 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['53', '56'])).
% 49.45/49.63  thf('58', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('59', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 49.45/49.63           (k3_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 49.45/49.63            (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))
% 49.45/49.63           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['57', '58'])).
% 49.45/49.63  thf('60', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('61', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['39', '40'])).
% 49.45/49.63  thf('62', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['60', '61'])).
% 49.45/49.63  thf('63', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('64', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['62', '63'])).
% 49.45/49.63  thf('65', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('66', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 49.45/49.63           (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 49.45/49.63            (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))
% 49.45/49.63           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['59', '64', '65'])).
% 49.45/49.63  thf('67', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0) @ 
% 49.45/49.63           (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))
% 49.45/49.63           = (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['48', '66'])).
% 49.45/49.63  thf('68', plain,
% 49.45/49.63      (![X7 : $i, X8 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 49.45/49.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 49.45/49.63  thf('69', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('70', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 49.45/49.63           = (k4_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['7', '8'])).
% 49.45/49.63  thf('71', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('72', plain,
% 49.45/49.63      (![X9 : $i, X10 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 49.45/49.63           = (k4_xboole_0 @ X9 @ X10))),
% 49.45/49.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 49.45/49.63  thf('73', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['71', '72'])).
% 49.45/49.63  thf('74', plain,
% 49.45/49.63      (![X16 : $i, X17 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 49.45/49.63           = (k3_xboole_0 @ X16 @ X17))),
% 49.45/49.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.45/49.63  thf('75', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['73', '74'])).
% 49.45/49.63  thf('76', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 49.45/49.63           = (k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 49.45/49.63              (k4_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['70', '75'])).
% 49.45/49.63  thf('77', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('78', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['39', '40'])).
% 49.45/49.63  thf('79', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('80', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['39', '40'])).
% 49.45/49.63  thf('81', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 49.45/49.63  thf('82', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ X1)
% 49.45/49.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)], ['73', '74'])).
% 49.45/49.63  thf('83', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['81', '82'])).
% 49.45/49.63  thf('84', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('85', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['31', '36'])).
% 49.45/49.63  thf('86', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['84', '85'])).
% 49.45/49.63  thf('87', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['83', '86'])).
% 49.45/49.63  thf('88', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 49.45/49.63           = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['69', '87'])).
% 49.45/49.63  thf('89', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 49.45/49.63           = (k1_xboole_0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['68', '88'])).
% 49.45/49.63  thf('90', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('92', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['12', '47'])).
% 49.45/49.63  thf('93', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 49.45/49.63           = (k4_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['67', '89', '90', '91', '92'])).
% 49.45/49.63  thf('94', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['39', '40'])).
% 49.45/49.63  thf('95', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('96', plain,
% 49.45/49.63      (![X18 : $i, X19 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 49.45/49.63           = (X18))),
% 49.45/49.63      inference('cnf', [status(esa)], [t51_xboole_1])).
% 49.45/49.63  thf('97', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['95', '96'])).
% 49.45/49.63  thf('98', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['94', '97'])).
% 49.45/49.63  thf('99', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 49.45/49.63           = (k4_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['7', '8'])).
% 49.45/49.63  thf('100', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('demod', [status(thm)], ['98', '99'])).
% 49.45/49.63  thf('101', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['93', '100'])).
% 49.45/49.63  thf('102', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('demod', [status(thm)], ['98', '99'])).
% 49.45/49.63  thf('103', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['101', '102'])).
% 49.45/49.63  thf('104', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['5', '103'])).
% 49.45/49.63  thf('105', plain,
% 49.45/49.63      (![X9 : $i, X10 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 49.45/49.63           = (k4_xboole_0 @ X9 @ X10))),
% 49.45/49.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 49.45/49.63  thf('106', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('107', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 49.45/49.63              (k4_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['105', '106'])).
% 49.45/49.63  thf('108', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('109', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 49.45/49.63      inference('demod', [status(thm)], ['107', '108'])).
% 49.45/49.63  thf('110', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('111', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['31', '36'])).
% 49.45/49.63  thf('112', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['110', '111'])).
% 49.45/49.63  thf('113', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('114', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('115', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['109', '112', '113', '114'])).
% 49.45/49.63  thf('116', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['104', '115'])).
% 49.45/49.63  thf('117', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 49.45/49.63  thf('118', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['1', '2'])).
% 49.45/49.63  thf('119', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('120', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('121', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 49.45/49.63              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))))),
% 49.45/49.63      inference('sup+', [status(thm)], ['119', '120'])).
% 49.45/49.63  thf('122', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 49.45/49.63           (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 49.45/49.63              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63               (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))))),
% 49.45/49.63      inference('sup+', [status(thm)], ['118', '121'])).
% 49.45/49.63  thf('123', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['3', '4'])).
% 49.45/49.63  thf('124', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('125', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63           (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)) @ 
% 49.45/49.63              (k4_xboole_0 @ X1 @ 
% 49.45/49.63               (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))))))),
% 49.45/49.63      inference('demod', [status(thm)], ['122', '123', '124'])).
% 49.45/49.63  thf('126', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 49.45/49.63           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)) @ 
% 49.45/49.63              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 49.45/49.63      inference('sup+', [status(thm)], ['117', '125'])).
% 49.45/49.63  thf('127', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 49.45/49.63  thf('128', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['3', '4'])).
% 49.45/49.63  thf('129', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('130', plain,
% 49.45/49.63      (![X7 : $i, X8 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 49.45/49.63      inference('cnf', [status(esa)], [t22_xboole_1])).
% 49.45/49.63  thf('131', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['129', '130'])).
% 49.45/49.63  thf('132', plain,
% 49.45/49.63      (![X9 : $i, X10 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 49.45/49.63           = (k4_xboole_0 @ X9 @ X10))),
% 49.45/49.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 49.45/49.63  thf('133', plain,
% 49.45/49.63      (![X16 : $i, X17 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 49.45/49.63           = (k3_xboole_0 @ X16 @ X17))),
% 49.45/49.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 49.45/49.63  thf('134', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('135', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['133', '134'])).
% 49.45/49.63  thf('136', plain,
% 49.45/49.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 49.45/49.63           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 49.45/49.63      inference('cnf', [status(esa)], [t41_xboole_1])).
% 49.45/49.63  thf('137', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['110', '111'])).
% 49.45/49.63  thf('138', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 49.45/49.63      inference('cnf', [status(esa)], [t1_boole])).
% 49.45/49.63  thf('139', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k3_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 49.45/49.63  thf('140', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['132', '139'])).
% 49.45/49.63  thf('141', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('142', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['14', '41'])).
% 49.45/49.63  thf('143', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['140', '141', '142'])).
% 49.45/49.63  thf('144', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 49.45/49.63           = (k3_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['131', '143'])).
% 49.45/49.63  thf('145', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('146', plain,
% 49.45/49.63      (![X14 : $i, X15 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 49.45/49.63           = (k4_xboole_0 @ X14 @ X15))),
% 49.45/49.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 49.45/49.63  thf('147', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['145', '146'])).
% 49.45/49.63  thf('148', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 49.45/49.63           = (k3_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['144', '147'])).
% 49.45/49.63  thf('149', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['14', '41'])).
% 49.45/49.63  thf('150', plain,
% 49.45/49.63      (![X14 : $i, X15 : $i]:
% 49.45/49.63         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 49.45/49.63           = (k4_xboole_0 @ X14 @ X15))),
% 49.45/49.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 49.45/49.63  thf('151', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('152', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 49.45/49.63              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['150', '151'])).
% 49.45/49.63  thf('153', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['84', '85'])).
% 49.45/49.63  thf('154', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('155', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('156', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k4_xboole_0 @ X1 @ X0))),
% 49.45/49.63      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 49.45/49.63  thf('157', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ X0)
% 49.45/49.63           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['149', '156'])).
% 49.45/49.63  thf('158', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 49.45/49.63  thf('159', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['27', '28'])).
% 49.45/49.63  thf('160', plain,
% 49.45/49.63      (![X4 : $i, X5 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X4 @ X5)
% 49.45/49.63           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 49.45/49.63      inference('cnf', [status(esa)], [d6_xboole_0])).
% 49.45/49.63  thf('161', plain,
% 49.45/49.63      (![X0 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ X0 @ X0)
% 49.45/49.63           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 49.45/49.63      inference('sup+', [status(thm)], ['159', '160'])).
% 49.45/49.63  thf('162', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['27', '28'])).
% 49.45/49.63  thf('163', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('164', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 49.45/49.63      inference('demod', [status(thm)], ['161', '162', '163'])).
% 49.45/49.63  thf('165', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 49.45/49.63      inference('sup+', [status(thm)], ['15', '16'])).
% 49.45/49.63  thf('166', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 49.45/49.63      inference('sup+', [status(thm)], ['164', '165'])).
% 49.45/49.63  thf('167', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k3_xboole_0 @ X1 @ X0)
% 49.45/49.63           = (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 49.45/49.63      inference('demod', [status(thm)],
% 49.45/49.63                ['126', '127', '128', '148', '157', '158', '166'])).
% 49.45/49.63  thf('168', plain,
% 49.45/49.63      (![X0 : $i, X1 : $i]:
% 49.45/49.63         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 49.45/49.63           = (k3_xboole_0 @ X0 @ X1))),
% 49.45/49.63      inference('demod', [status(thm)], ['116', '167'])).
% 49.45/49.63  thf('169', plain,
% 49.45/49.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 49.45/49.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 49.45/49.63  thf('170', plain,
% 49.45/49.63      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 49.45/49.63      inference('demod', [status(thm)], ['0', '168', '169'])).
% 49.45/49.63  thf('171', plain, ($false), inference('simplify', [status(thm)], ['170'])).
% 49.45/49.63  
% 49.45/49.63  % SZS output end Refutation
% 49.45/49.63  
% 49.45/49.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
