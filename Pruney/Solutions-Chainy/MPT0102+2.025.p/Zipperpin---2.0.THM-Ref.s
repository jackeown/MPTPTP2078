%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AggbiGzu58

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:01 EST 2020

% Result     : Theorem 45.90s
% Output     : Refutation 45.90s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 151 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  767 (1295 expanded)
%              Number of equality atoms :   82 ( 144 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','40','47','48','49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','28','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k2_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AggbiGzu58
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:07:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 45.90/46.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 45.90/46.19  % Solved by: fo/fo7.sh
% 45.90/46.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.90/46.19  % done 7915 iterations in 45.728s
% 45.90/46.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 45.90/46.19  % SZS output start Refutation
% 45.90/46.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 45.90/46.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 45.90/46.19  thf(sk_A_type, type, sk_A: $i).
% 45.90/46.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 45.90/46.19  thf(sk_B_type, type, sk_B: $i).
% 45.90/46.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 45.90/46.19  thf(t95_xboole_1, conjecture,
% 45.90/46.19    (![A:$i,B:$i]:
% 45.90/46.19     ( ( k3_xboole_0 @ A @ B ) =
% 45.90/46.19       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 45.90/46.19  thf(zf_stmt_0, negated_conjecture,
% 45.90/46.19    (~( ![A:$i,B:$i]:
% 45.90/46.19        ( ( k3_xboole_0 @ A @ B ) =
% 45.90/46.19          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 45.90/46.19    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 45.90/46.19  thf('0', plain,
% 45.90/46.19      (((k3_xboole_0 @ sk_A @ sk_B)
% 45.90/46.19         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 45.90/46.19             (k2_xboole_0 @ sk_A @ sk_B)))),
% 45.90/46.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.90/46.19  thf(l98_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i]:
% 45.90/46.19     ( ( k5_xboole_0 @ A @ B ) =
% 45.90/46.19       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 45.90/46.19  thf('1', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf(t48_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i]:
% 45.90/46.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 45.90/46.19  thf('2', plain,
% 45.90/46.19      (![X14 : $i, X15 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 45.90/46.19           = (k3_xboole_0 @ X14 @ X15))),
% 45.90/46.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.90/46.19  thf('3', plain,
% 45.90/46.19      (![X14 : $i, X15 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 45.90/46.19           = (k3_xboole_0 @ X14 @ X15))),
% 45.90/46.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.90/46.19  thf('4', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['2', '3'])).
% 45.90/46.19  thf(t47_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i]:
% 45.90/46.19     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 45.90/46.19  thf('5', plain,
% 45.90/46.19      (![X12 : $i, X13 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 45.90/46.19           = (k4_xboole_0 @ X12 @ X13))),
% 45.90/46.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 45.90/46.19  thf('6', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k4_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['4', '5'])).
% 45.90/46.19  thf(t22_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 45.90/46.19  thf('7', plain,
% 45.90/46.19      (![X10 : $i, X11 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 45.90/46.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 45.90/46.19  thf('8', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 45.90/46.19      inference('sup+', [status(thm)], ['6', '7'])).
% 45.90/46.19  thf(commutativity_k2_xboole_0, axiom,
% 45.90/46.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 45.90/46.19  thf('9', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.90/46.19  thf(t21_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 45.90/46.19  thf('10', plain,
% 45.90/46.19      (![X8 : $i, X9 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 45.90/46.19      inference('cnf', [status(esa)], [t21_xboole_1])).
% 45.90/46.19  thf('11', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['9', '10'])).
% 45.90/46.19  thf('12', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf('13', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['11', '12'])).
% 45.90/46.19  thf(idempotence_k2_xboole_0, axiom,
% 45.90/46.19    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 45.90/46.19  thf('14', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 45.90/46.19      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 45.90/46.19  thf(t4_xboole_1, axiom,
% 45.90/46.19    (![A:$i,B:$i,C:$i]:
% 45.90/46.19     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 45.90/46.19       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 45.90/46.19  thf('15', plain,
% 45.90/46.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 45.90/46.19           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 45.90/46.19      inference('cnf', [status(esa)], [t4_xboole_1])).
% 45.90/46.19  thf('16', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.90/46.19  thf('17', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 45.90/46.19           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['15', '16'])).
% 45.90/46.19  thf('18', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k2_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['14', '17'])).
% 45.90/46.19  thf('19', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 45.90/46.19      inference('demod', [status(thm)], ['13', '18'])).
% 45.90/46.19  thf('20', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 45.90/46.19           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 45.90/46.19           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['8', '19'])).
% 45.90/46.19  thf('21', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 45.90/46.19      inference('sup+', [status(thm)], ['6', '7'])).
% 45.90/46.19  thf(commutativity_k3_xboole_0, axiom,
% 45.90/46.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 45.90/46.19  thf('22', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('23', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf('24', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ X1)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['22', '23'])).
% 45.90/46.19  thf('25', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 45.90/46.19  thf('26', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf('27', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ X1)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['25', '26'])).
% 45.90/46.19  thf('28', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['24', '27'])).
% 45.90/46.19  thf('29', plain,
% 45.90/46.19      (![X12 : $i, X13 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 45.90/46.19           = (k4_xboole_0 @ X12 @ X13))),
% 45.90/46.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 45.90/46.19  thf('30', plain,
% 45.90/46.19      (![X14 : $i, X15 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 45.90/46.19           = (k3_xboole_0 @ X14 @ X15))),
% 45.90/46.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.90/46.19  thf('31', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['29', '30'])).
% 45.90/46.19  thf('32', plain,
% 45.90/46.19      (![X14 : $i, X15 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 45.90/46.19           = (k3_xboole_0 @ X14 @ X15))),
% 45.90/46.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.90/46.19  thf('33', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X1 @ X0)
% 45.90/46.19           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('demod', [status(thm)], ['31', '32'])).
% 45.90/46.19  thf('34', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf('35', plain,
% 45.90/46.19      (![X14 : $i, X15 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 45.90/46.19           = (k3_xboole_0 @ X14 @ X15))),
% 45.90/46.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 45.90/46.19  thf('36', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['34', '35'])).
% 45.90/46.19  thf('37', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('38', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('demod', [status(thm)], ['36', '37'])).
% 45.90/46.19  thf('39', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 45.90/46.19           (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 45.90/46.19           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 45.90/46.19              (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 45.90/46.19      inference('sup+', [status(thm)], ['33', '38'])).
% 45.90/46.19  thf('40', plain,
% 45.90/46.19      (![X10 : $i, X11 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 45.90/46.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 45.90/46.19  thf('41', plain,
% 45.90/46.19      (![X10 : $i, X11 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 45.90/46.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 45.90/46.19  thf('42', plain,
% 45.90/46.19      (![X6 : $i, X7 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X6 @ X7)
% 45.90/46.19           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 45.90/46.19      inference('cnf', [status(esa)], [l98_xboole_1])).
% 45.90/46.19  thf('43', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 45.90/46.19           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 45.90/46.19      inference('sup+', [status(thm)], ['41', '42'])).
% 45.90/46.19  thf('44', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X1 @ X0)
% 45.90/46.19           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('demod', [status(thm)], ['31', '32'])).
% 45.90/46.19  thf('45', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 45.90/46.19           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 45.90/46.19      inference('demod', [status(thm)], ['43', '44'])).
% 45.90/46.19  thf('46', plain,
% 45.90/46.19      (![X12 : $i, X13 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 45.90/46.19           = (k4_xboole_0 @ X12 @ X13))),
% 45.90/46.19      inference('cnf', [status(esa)], [t47_xboole_1])).
% 45.90/46.19  thf('47', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k4_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['45', '46'])).
% 45.90/46.19  thf('48', plain,
% 45.90/46.19      (![X10 : $i, X11 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 45.90/46.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 45.90/46.19  thf('49', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('50', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('51', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('52', plain,
% 45.90/46.19      (![X10 : $i, X11 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 45.90/46.19      inference('cnf', [status(esa)], [t22_xboole_1])).
% 45.90/46.19  thf('53', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['51', '52'])).
% 45.90/46.19  thf('54', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['9', '10'])).
% 45.90/46.19  thf('55', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 45.90/46.19           = (k3_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['53', '54'])).
% 45.90/46.19  thf('56', plain,
% 45.90/46.19      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 45.90/46.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.90/46.19  thf('57', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('demod', [status(thm)], ['55', '56'])).
% 45.90/46.19  thf('58', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X0 @ X1))),
% 45.90/46.19      inference('sup+', [status(thm)], ['50', '57'])).
% 45.90/46.19  thf('59', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X0 @ X1))),
% 45.90/46.19      inference('demod', [status(thm)], ['39', '40', '47', '48', '49', '58'])).
% 45.90/46.19  thf('60', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('demod', [status(thm)], ['20', '21', '28', '59'])).
% 45.90/46.19  thf('61', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('sup+', [status(thm)], ['1', '60'])).
% 45.90/46.19  thf('62', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['24', '27'])).
% 45.90/46.19  thf('63', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 45.90/46.19      inference('demod', [status(thm)], ['61', '62'])).
% 45.90/46.19  thf('64', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['51', '52'])).
% 45.90/46.19  thf('65', plain,
% 45.90/46.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 45.90/46.19         ((k2_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X18)
% 45.90/46.19           = (k2_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 45.90/46.19      inference('cnf', [status(esa)], [t4_xboole_1])).
% 45.90/46.19  thf('66', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['9', '10'])).
% 45.90/46.19  thf('67', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 45.90/46.19           = (X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['65', '66'])).
% 45.90/46.19  thf('68', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.90/46.19         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('sup+', [status(thm)], ['64', '67'])).
% 45.90/46.19  thf('69', plain,
% 45.90/46.19      (![X0 : $i, X1 : $i]:
% 45.90/46.19         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.90/46.19           = (k3_xboole_0 @ X1 @ X0))),
% 45.90/46.19      inference('demod', [status(thm)], ['63', '68'])).
% 45.90/46.19  thf('70', plain,
% 45.90/46.19      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 45.90/46.19      inference('demod', [status(thm)], ['0', '69'])).
% 45.90/46.19  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 45.90/46.19  
% 45.90/46.19  % SZS output end Refutation
% 45.90/46.19  
% 45.90/46.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
