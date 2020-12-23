%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OXbsCXbBE8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:21 EST 2020

% Result     : Theorem 14.77s
% Output     : Refutation 14.77s
% Verified   : 
% Statistics : Number of formulae       :  149 (1019 expanded)
%              Number of leaves         :   22 ( 356 expanded)
%              Depth                    :   27
%              Number of atoms          : 1170 (7211 expanded)
%              Number of equality atoms :  136 (1005 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t101_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t101_xboole_1])).

thf('0',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
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

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['36','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','56','61'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ ( k5_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('82',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','62','63','76','77','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','97'])).

thf('99',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ X28 )
      = ( k5_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('101',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','86'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','104'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('116',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ ( k5_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','117','122'])).

thf('124',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','123'])).

thf('125',plain,(
    $false ),
    inference(simplify,[status(thm)],['124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OXbsCXbBE8
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:11:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 14.77/14.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.77/14.96  % Solved by: fo/fo7.sh
% 14.77/14.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.77/14.96  % done 7989 iterations in 14.493s
% 14.77/14.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.77/14.96  % SZS output start Refutation
% 14.77/14.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 14.77/14.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.77/14.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 14.77/14.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.77/14.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.77/14.96  thf(sk_A_type, type, sk_A: $i).
% 14.77/14.96  thf(sk_B_type, type, sk_B: $i).
% 14.77/14.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 14.77/14.96  thf(t101_xboole_1, conjecture,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k5_xboole_0 @ A @ B ) =
% 14.77/14.96       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.77/14.96  thf(zf_stmt_0, negated_conjecture,
% 14.77/14.96    (~( ![A:$i,B:$i]:
% 14.77/14.96        ( ( k5_xboole_0 @ A @ B ) =
% 14.77/14.96          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 14.77/14.96    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 14.77/14.96  thf('0', plain,
% 14.77/14.96      (((k5_xboole_0 @ sk_A @ sk_B)
% 14.77/14.96         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 14.77/14.96             (k3_xboole_0 @ sk_A @ sk_B)))),
% 14.77/14.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.77/14.96  thf(commutativity_k3_xboole_0, axiom,
% 14.77/14.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 14.77/14.96  thf('1', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf(t93_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k2_xboole_0 @ A @ B ) =
% 14.77/14.96       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.77/14.96  thf('2', plain,
% 14.77/14.96      (![X25 : $i, X26 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X25 @ X26)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 14.77/14.96              (k3_xboole_0 @ X25 @ X26)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t93_xboole_1])).
% 14.77/14.96  thf('3', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['1', '2'])).
% 14.77/14.96  thf(t46_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 14.77/14.96  thf('4', plain,
% 14.77/14.96      (![X10 : $i, X11 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 14.77/14.96      inference('cnf', [status(esa)], [t46_xboole_1])).
% 14.77/14.96  thf(t48_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.77/14.96  thf('5', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('6', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 14.77/14.96           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['4', '5'])).
% 14.77/14.96  thf(idempotence_k2_xboole_0, axiom,
% 14.77/14.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 14.77/14.96  thf('7', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 14.77/14.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.77/14.96  thf('8', plain,
% 14.77/14.96      (![X10 : $i, X11 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 14.77/14.96      inference('cnf', [status(esa)], [t46_xboole_1])).
% 14.77/14.96  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['7', '8'])).
% 14.77/14.96  thf('10', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('11', plain,
% 14.77/14.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['9', '10'])).
% 14.77/14.96  thf(t47_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 14.77/14.96  thf('12', plain,
% 14.77/14.96      (![X12 : $i, X13 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 14.77/14.96           = (k4_xboole_0 @ X12 @ X13))),
% 14.77/14.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 14.77/14.96  thf('13', plain,
% 14.77/14.96      (![X0 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 14.77/14.96           = (k4_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['11', '12'])).
% 14.77/14.96  thf('14', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['7', '8'])).
% 14.77/14.96  thf('16', plain,
% 14.77/14.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['13', '14', '15'])).
% 14.77/14.96  thf(t100_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 14.77/14.96  thf('17', plain,
% 14.77/14.96      (![X5 : $i, X6 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X5 @ X6)
% 14.77/14.96           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 14.77/14.96  thf('18', plain,
% 14.77/14.96      (![X0 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['16', '17'])).
% 14.77/14.96  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['7', '8'])).
% 14.77/14.96  thf(t98_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 14.77/14.96  thf('20', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('21', plain,
% 14.77/14.96      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['19', '20'])).
% 14.77/14.96  thf('22', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 14.77/14.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.77/14.96  thf('23', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['21', '22'])).
% 14.77/14.96  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['18', '23'])).
% 14.77/14.96  thf('25', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('demod', [status(thm)], ['6', '24'])).
% 14.77/14.96  thf('26', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('27', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('28', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('29', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('30', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 14.77/14.96           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['28', '29'])).
% 14.77/14.96  thf('31', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['1', '2'])).
% 14.77/14.96  thf('32', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 14.77/14.96           = (k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) @ 
% 14.77/14.96              (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))))),
% 14.77/14.96      inference('sup+', [status(thm)], ['30', '31'])).
% 14.77/14.96  thf('33', plain,
% 14.77/14.96      (![X5 : $i, X6 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X5 @ X6)
% 14.77/14.96           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 14.77/14.96  thf('34', plain,
% 14.77/14.96      (![X25 : $i, X26 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X25 @ X26)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 14.77/14.96              (k3_xboole_0 @ X25 @ X26)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t93_xboole_1])).
% 14.77/14.96  thf('35', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 14.77/14.96              (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 14.77/14.96      inference('sup+', [status(thm)], ['33', '34'])).
% 14.77/14.96  thf('36', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('37', plain,
% 14.77/14.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['9', '10'])).
% 14.77/14.96  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['18', '23'])).
% 14.77/14.96  thf('39', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['37', '38'])).
% 14.77/14.96  thf(t49_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i,C:$i]:
% 14.77/14.96     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 14.77/14.96       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 14.77/14.96  thf('40', plain,
% 14.77/14.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.77/14.96           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 14.77/14.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 14.77/14.96  thf('41', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.77/14.96           = (k4_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('sup+', [status(thm)], ['39', '40'])).
% 14.77/14.96  thf('42', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('43', plain,
% 14.77/14.96      (![X5 : $i, X6 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X5 @ X6)
% 14.77/14.96           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 14.77/14.96  thf('44', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['42', '43'])).
% 14.77/14.96  thf('45', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 14.77/14.96           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['41', '44'])).
% 14.77/14.96  thf('46', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['37', '38'])).
% 14.77/14.96  thf('47', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['42', '43'])).
% 14.77/14.96  thf('48', plain,
% 14.77/14.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['46', '47'])).
% 14.77/14.96  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['7', '8'])).
% 14.77/14.96  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['48', '49'])).
% 14.77/14.96  thf('51', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['45', '50'])).
% 14.77/14.96  thf('52', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('53', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 14.77/14.96           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['51', '52'])).
% 14.77/14.96  thf('54', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['21', '22'])).
% 14.77/14.96  thf('55', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['53', '54'])).
% 14.77/14.96  thf('56', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 14.77/14.96      inference('sup+', [status(thm)], ['36', '55'])).
% 14.77/14.96  thf('57', plain,
% 14.77/14.96      (![X12 : $i, X13 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13))
% 14.77/14.96           = (k4_xboole_0 @ X12 @ X13))),
% 14.77/14.96      inference('cnf', [status(esa)], [t47_xboole_1])).
% 14.77/14.96  thf('58', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('59', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['57', '58'])).
% 14.77/14.96  thf('60', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('61', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X1 @ X0)
% 14.77/14.96           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('demod', [status(thm)], ['59', '60'])).
% 14.77/14.96  thf('62', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X1)
% 14.77/14.96           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('demod', [status(thm)], ['35', '56', '61'])).
% 14.77/14.96  thf(t16_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i,C:$i]:
% 14.77/14.96     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 14.77/14.96       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 14.77/14.96  thf('63', plain,
% 14.77/14.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 14.77/14.96           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 14.77/14.96  thf('64', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('65', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf(l97_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 14.77/14.96  thf('66', plain,
% 14.77/14.96      (![X3 : $i, X4 : $i]:
% 14.77/14.96         (r1_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ (k5_xboole_0 @ X3 @ X4))),
% 14.77/14.96      inference('cnf', [status(esa)], [l97_xboole_1])).
% 14.77/14.96  thf('67', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('sup+', [status(thm)], ['65', '66'])).
% 14.77/14.96  thf(t83_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i]:
% 14.77/14.96     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.77/14.96  thf('68', plain,
% 14.77/14.96      (![X19 : $i, X20 : $i]:
% 14.77/14.96         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 14.77/14.96      inference('cnf', [status(esa)], [t83_xboole_1])).
% 14.77/14.96  thf('69', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('sup-', [status(thm)], ['67', '68'])).
% 14.77/14.96  thf('70', plain,
% 14.77/14.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.77/14.96           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 14.77/14.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 14.77/14.96  thf('71', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 14.77/14.96           = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('demod', [status(thm)], ['69', '70'])).
% 14.77/14.96  thf('72', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 14.77/14.96           (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 14.77/14.96           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 14.77/14.96      inference('sup+', [status(thm)], ['64', '71'])).
% 14.77/14.96  thf('73', plain,
% 14.77/14.96      (![X10 : $i, X11 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 14.77/14.96      inference('cnf', [status(esa)], [t46_xboole_1])).
% 14.77/14.96  thf('74', plain,
% 14.77/14.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['13', '14', '15'])).
% 14.77/14.96  thf('75', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('76', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 14.77/14.96      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 14.77/14.96  thf('77', plain,
% 14.77/14.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['13', '14', '15'])).
% 14.77/14.96  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['18', '23'])).
% 14.77/14.96  thf('79', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('80', plain,
% 14.77/14.96      (![X0 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['78', '79'])).
% 14.77/14.96  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['48', '49'])).
% 14.77/14.96  thf('82', plain,
% 14.77/14.96      (![X25 : $i, X26 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X25 @ X26)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 14.77/14.96              (k3_xboole_0 @ X25 @ X26)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t93_xboole_1])).
% 14.77/14.96  thf('83', plain,
% 14.77/14.96      (![X0 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ X0)
% 14.77/14.96           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['81', '82'])).
% 14.77/14.96  thf('84', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 14.77/14.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 14.77/14.96  thf('85', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['37', '38'])).
% 14.77/14.96  thf('86', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['83', '84', '85'])).
% 14.77/14.96  thf('87', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['80', '86'])).
% 14.77/14.96  thf('88', plain,
% 14.77/14.96      (![X25 : $i, X26 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X25 @ X26)
% 14.77/14.96           = (k2_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 14.77/14.96              (k3_xboole_0 @ X25 @ X26)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t93_xboole_1])).
% 14.77/14.96  thf('89', plain,
% 14.77/14.96      (![X0 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 14.77/14.96           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['87', '88'])).
% 14.77/14.96  thf('90', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['83', '84', '85'])).
% 14.77/14.96  thf('91', plain,
% 14.77/14.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['13', '14', '15'])).
% 14.77/14.96  thf('92', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('93', plain,
% 14.77/14.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['91', '92'])).
% 14.77/14.96  thf('94', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 14.77/14.96      inference('demod', [status(thm)], ['89', '90', '93'])).
% 14.77/14.96  thf('95', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['32', '62', '63', '76', '77', '94'])).
% 14.77/14.96  thf('96', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 14.77/14.96      inference('sup+', [status(thm)], ['27', '95'])).
% 14.77/14.96  thf('97', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['26', '96'])).
% 14.77/14.96  thf('98', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['25', '97'])).
% 14.77/14.96  thf('99', plain,
% 14.77/14.96      (![X27 : $i, X28 : $i]:
% 14.77/14.96         ((k2_xboole_0 @ X27 @ X28)
% 14.77/14.96           = (k5_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 14.77/14.96  thf('100', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['48', '49'])).
% 14.77/14.96  thf(t91_xboole_1, axiom,
% 14.77/14.96    (![A:$i,B:$i,C:$i]:
% 14.77/14.96     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 14.77/14.96       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 14.77/14.96  thf('101', plain,
% 14.77/14.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 14.77/14.96         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 14.77/14.96           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 14.77/14.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 14.77/14.96  thf('102', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 14.77/14.96           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['100', '101'])).
% 14.77/14.96  thf('103', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['80', '86'])).
% 14.77/14.96  thf('104', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('demod', [status(thm)], ['102', '103'])).
% 14.77/14.96  thf('105', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['99', '104'])).
% 14.77/14.96  thf('106', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 14.77/14.96           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['98', '105'])).
% 14.77/14.96  thf('107', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X0 @ X1)
% 14.77/14.96           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('sup+', [status(thm)], ['99', '104'])).
% 14.77/14.96  thf('108', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 14.77/14.96           = (k4_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('demod', [status(thm)], ['106', '107'])).
% 14.77/14.96  thf('109', plain,
% 14.77/14.96      (![X14 : $i, X15 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 14.77/14.96           = (k3_xboole_0 @ X14 @ X15))),
% 14.77/14.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.77/14.96  thf('110', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['108', '109'])).
% 14.77/14.96  thf('111', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('112', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 14.77/14.96      inference('demod', [status(thm)], ['6', '24'])).
% 14.77/14.96  thf('113', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['110', '111', '112'])).
% 14.77/14.96  thf('114', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 14.77/14.96           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))
% 14.77/14.96           = (k5_xboole_0 @ X1 @ X0))),
% 14.77/14.96      inference('sup+', [status(thm)], ['3', '113'])).
% 14.77/14.96  thf('115', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 14.77/14.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 14.77/14.96  thf('116', plain,
% 14.77/14.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.77/14.96           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 14.77/14.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 14.77/14.96  thf('117', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 14.77/14.96           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 14.77/14.96      inference('sup+', [status(thm)], ['115', '116'])).
% 14.77/14.96  thf('118', plain,
% 14.77/14.96      (![X3 : $i, X4 : $i]:
% 14.77/14.96         (r1_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ (k5_xboole_0 @ X3 @ X4))),
% 14.77/14.96      inference('cnf', [status(esa)], [l97_xboole_1])).
% 14.77/14.96  thf('119', plain,
% 14.77/14.96      (![X19 : $i, X20 : $i]:
% 14.77/14.96         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 14.77/14.96      inference('cnf', [status(esa)], [t83_xboole_1])).
% 14.77/14.96  thf('120', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k3_xboole_0 @ X1 @ X0))),
% 14.77/14.96      inference('sup-', [status(thm)], ['118', '119'])).
% 14.77/14.96  thf('121', plain,
% 14.77/14.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 14.77/14.96           = (k4_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X18))),
% 14.77/14.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 14.77/14.96  thf('122', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 14.77/14.96           = (k3_xboole_0 @ X1 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['120', '121'])).
% 14.77/14.96  thf('123', plain,
% 14.77/14.96      (![X0 : $i, X1 : $i]:
% 14.77/14.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 14.77/14.96           = (k5_xboole_0 @ X1 @ X0))),
% 14.77/14.96      inference('demod', [status(thm)], ['114', '117', '122'])).
% 14.77/14.96  thf('124', plain,
% 14.77/14.96      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 14.77/14.96      inference('demod', [status(thm)], ['0', '123'])).
% 14.77/14.96  thf('125', plain, ($false), inference('simplify', [status(thm)], ['124'])).
% 14.77/14.96  
% 14.77/14.96  % SZS output end Refutation
% 14.77/14.96  
% 14.77/14.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
