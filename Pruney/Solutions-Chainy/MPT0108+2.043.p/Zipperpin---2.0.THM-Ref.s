%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzwhuziCIG

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:22 EST 2020

% Result     : Theorem 47.52s
% Output     : Refutation 47.52s
% Verified   : 
% Statistics : Number of formulae       :  150 (4329 expanded)
%              Number of leaves         :   19 (1481 expanded)
%              Depth                    :   24
%              Number of atoms          : 1183 (30198 expanded)
%              Number of equality atoms :  142 (4321 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
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
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','23'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','45'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','23'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','45'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','79','80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['84','90'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['91','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('104',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('110',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','45'])).

thf('114',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','45'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['111','121','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','105','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('128',plain,(
    ( k5_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','126','127'])).

thf('129',plain,(
    $false ),
    inference(simplify,[status(thm)],['128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzwhuziCIG
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 47.52/47.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.52/47.79  % Solved by: fo/fo7.sh
% 47.52/47.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.52/47.79  % done 13351 iterations in 47.330s
% 47.52/47.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.52/47.79  % SZS output start Refutation
% 47.52/47.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 47.52/47.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.52/47.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 47.52/47.79  thf(sk_A_type, type, sk_A: $i).
% 47.52/47.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 47.52/47.79  thf(sk_B_type, type, sk_B: $i).
% 47.52/47.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 47.52/47.79  thf(t101_xboole_1, conjecture,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k5_xboole_0 @ A @ B ) =
% 47.52/47.79       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 47.52/47.79  thf(zf_stmt_0, negated_conjecture,
% 47.52/47.79    (~( ![A:$i,B:$i]:
% 47.52/47.79        ( ( k5_xboole_0 @ A @ B ) =
% 47.52/47.79          ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 47.52/47.79    inference('cnf.neg', [status(esa)], [t101_xboole_1])).
% 47.52/47.79  thf('0', plain,
% 47.52/47.79      (((k5_xboole_0 @ sk_A @ sk_B)
% 47.52/47.79         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 47.52/47.79             (k3_xboole_0 @ sk_A @ sk_B)))),
% 47.52/47.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.52/47.79  thf(idempotence_k2_xboole_0, axiom,
% 47.52/47.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 47.52/47.79  thf('1', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 47.52/47.79      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 47.52/47.79  thf(t46_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 47.52/47.79  thf('2', plain,
% 47.52/47.79      (![X6 : $i, X7 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 47.52/47.79      inference('cnf', [status(esa)], [t46_xboole_1])).
% 47.52/47.79  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['1', '2'])).
% 47.52/47.79  thf(t48_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 47.52/47.79  thf('4', plain,
% 47.52/47.79      (![X10 : $i, X11 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 47.52/47.79           = (k3_xboole_0 @ X10 @ X11))),
% 47.52/47.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.52/47.79  thf('5', plain,
% 47.52/47.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['3', '4'])).
% 47.52/47.79  thf('6', plain,
% 47.52/47.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['3', '4'])).
% 47.52/47.79  thf(t47_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 47.52/47.79  thf('7', plain,
% 47.52/47.79      (![X8 : $i, X9 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 47.52/47.79           = (k4_xboole_0 @ X8 @ X9))),
% 47.52/47.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 47.52/47.79  thf('8', plain,
% 47.52/47.79      (![X0 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 47.52/47.79           = (k4_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['6', '7'])).
% 47.52/47.79  thf('9', plain,
% 47.52/47.79      (![X10 : $i, X11 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 47.52/47.79           = (k3_xboole_0 @ X10 @ X11))),
% 47.52/47.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.52/47.79  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['1', '2'])).
% 47.52/47.79  thf('11', plain,
% 47.52/47.79      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['8', '9', '10'])).
% 47.52/47.79  thf(commutativity_k3_xboole_0, axiom,
% 47.52/47.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 47.52/47.79  thf('12', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.52/47.79  thf('13', plain,
% 47.52/47.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['11', '12'])).
% 47.52/47.79  thf('14', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.52/47.79  thf(t100_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 47.52/47.79  thf('15', plain,
% 47.52/47.79      (![X3 : $i, X4 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X3 @ X4)
% 47.52/47.79           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.52/47.79  thf('16', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['14', '15'])).
% 47.52/47.79  thf('17', plain,
% 47.52/47.79      (![X0 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['13', '16'])).
% 47.52/47.79  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['1', '2'])).
% 47.52/47.79  thf(t98_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 47.52/47.79  thf('19', plain,
% 47.52/47.79      (![X20 : $i, X21 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X20 @ X21)
% 47.52/47.79           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.52/47.79  thf('20', plain,
% 47.52/47.79      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['18', '19'])).
% 47.52/47.79  thf('21', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 47.52/47.79      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 47.52/47.79  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['20', '21'])).
% 47.52/47.79  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['17', '22'])).
% 47.52/47.79  thf('24', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['5', '23'])).
% 47.52/47.79  thf('25', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['14', '15'])).
% 47.52/47.79  thf('26', plain,
% 47.52/47.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['24', '25'])).
% 47.52/47.79  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['1', '2'])).
% 47.52/47.79  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['26', '27'])).
% 47.52/47.79  thf(t91_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i,C:$i]:
% 47.52/47.79     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 47.52/47.79       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 47.52/47.79  thf('29', plain,
% 47.52/47.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 47.52/47.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.52/47.79  thf('30', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k1_xboole_0)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 47.52/47.79      inference('sup+', [status(thm)], ['28', '29'])).
% 47.52/47.79  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['26', '27'])).
% 47.52/47.79  thf('32', plain,
% 47.52/47.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 47.52/47.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.52/47.79  thf('33', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['31', '32'])).
% 47.52/47.79  thf('34', plain,
% 47.52/47.79      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['11', '12'])).
% 47.52/47.79  thf(t93_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i]:
% 47.52/47.79     ( ( k2_xboole_0 @ A @ B ) =
% 47.52/47.79       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 47.52/47.79  thf('35', plain,
% 47.52/47.79      (![X18 : $i, X19 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X18 @ X19)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 47.52/47.79              (k3_xboole_0 @ X18 @ X19)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t93_xboole_1])).
% 47.52/47.79  thf('36', plain,
% 47.52/47.79      (![X0 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['34', '35'])).
% 47.52/47.79  thf(t1_boole, axiom,
% 47.52/47.79    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 47.52/47.79  thf('37', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 47.52/47.79      inference('cnf', [status(esa)], [t1_boole])).
% 47.52/47.79  thf('38', plain,
% 47.52/47.79      (![X0 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['36', '37'])).
% 47.52/47.79  thf('39', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['33', '38'])).
% 47.52/47.79  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['26', '27'])).
% 47.52/47.79  thf('41', plain,
% 47.52/47.79      (![X18 : $i, X19 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X18 @ X19)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 47.52/47.79              (k3_xboole_0 @ X18 @ X19)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t93_xboole_1])).
% 47.52/47.79  thf('42', plain,
% 47.52/47.79      (![X0 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X0)
% 47.52/47.79           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['40', '41'])).
% 47.52/47.79  thf('43', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 47.52/47.79      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 47.52/47.79  thf('44', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['5', '23'])).
% 47.52/47.79  thf('45', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['42', '43', '44'])).
% 47.52/47.79  thf('46', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['39', '45'])).
% 47.52/47.79  thf('47', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 47.52/47.79           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['30', '46'])).
% 47.52/47.79  thf('48', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['20', '21'])).
% 47.52/47.79  thf('49', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['47', '48'])).
% 47.52/47.79  thf('50', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['39', '45'])).
% 47.52/47.79  thf('51', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['49', '50'])).
% 47.52/47.79  thf('52', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.52/47.79  thf('53', plain,
% 47.52/47.79      (![X18 : $i, X19 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X18 @ X19)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 47.52/47.79              (k3_xboole_0 @ X18 @ X19)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t93_xboole_1])).
% 47.52/47.79  thf('54', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['52', '53'])).
% 47.52/47.79  thf('55', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['51', '54'])).
% 47.52/47.79  thf('56', plain,
% 47.52/47.79      (![X6 : $i, X7 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 47.52/47.79      inference('cnf', [status(esa)], [t46_xboole_1])).
% 47.52/47.79  thf('57', plain,
% 47.52/47.79      (![X10 : $i, X11 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 47.52/47.79           = (k3_xboole_0 @ X10 @ X11))),
% 47.52/47.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.52/47.79  thf('58', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 47.52/47.79           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['56', '57'])).
% 47.52/47.79  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['17', '22'])).
% 47.52/47.79  thf('60', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['58', '59'])).
% 47.52/47.79  thf('61', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['52', '53'])).
% 47.52/47.79  thf('62', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['60', '61'])).
% 47.52/47.79  thf('63', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['58', '59'])).
% 47.52/47.79  thf('64', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.52/47.79  thf('65', plain,
% 47.52/47.79      (![X10 : $i, X11 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 47.52/47.79           = (k3_xboole_0 @ X10 @ X11))),
% 47.52/47.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.52/47.79  thf('66', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['5', '23'])).
% 47.52/47.79  thf(t49_xboole_1, axiom,
% 47.52/47.79    (![A:$i,B:$i,C:$i]:
% 47.52/47.79     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 47.52/47.79       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 47.52/47.79  thf('67', plain,
% 47.52/47.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 47.52/47.79           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 47.52/47.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 47.52/47.79  thf('68', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 47.52/47.79           = (k4_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('sup+', [status(thm)], ['66', '67'])).
% 47.52/47.79  thf('69', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['14', '15'])).
% 47.52/47.79  thf('70', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 47.52/47.79           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['68', '69'])).
% 47.52/47.79  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['26', '27'])).
% 47.52/47.79  thf('72', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['70', '71'])).
% 47.52/47.79  thf('73', plain,
% 47.52/47.79      (![X20 : $i, X21 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X20 @ X21)
% 47.52/47.79           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.52/47.79  thf('74', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 47.52/47.79           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['72', '73'])).
% 47.52/47.79  thf('75', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['20', '21'])).
% 47.52/47.79  thf('76', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['74', '75'])).
% 47.52/47.79  thf('77', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 47.52/47.79      inference('sup+', [status(thm)], ['65', '76'])).
% 47.52/47.79  thf('78', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['64', '77'])).
% 47.52/47.79  thf('79', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 47.52/47.79           = (k2_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('sup+', [status(thm)], ['63', '78'])).
% 47.52/47.79  thf('80', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['49', '50'])).
% 47.52/47.79  thf('81', plain,
% 47.52/47.79      (![X20 : $i, X21 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X20 @ X21)
% 47.52/47.79           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 47.52/47.79  thf('82', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['39', '45'])).
% 47.52/47.79  thf('83', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['81', '82'])).
% 47.52/47.79  thf('84', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['62', '79', '80', '83'])).
% 47.52/47.79  thf('85', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['58', '59'])).
% 47.52/47.79  thf('86', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['14', '15'])).
% 47.52/47.79  thf('87', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 47.52/47.79           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['85', '86'])).
% 47.52/47.79  thf('88', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['49', '50'])).
% 47.52/47.79  thf('89', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['81', '82'])).
% 47.52/47.79  thf('90', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 47.52/47.79           = (k4_xboole_0 @ X1 @ X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['87', '88', '89'])).
% 47.52/47.79  thf('91', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 47.52/47.79           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['84', '90'])).
% 47.52/47.79  thf('92', plain,
% 47.52/47.79      (![X10 : $i, X11 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 47.52/47.79           = (k3_xboole_0 @ X10 @ X11))),
% 47.52/47.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 47.52/47.79  thf('93', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['70', '71'])).
% 47.52/47.79  thf('94', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['92', '93'])).
% 47.52/47.79  thf('95', plain,
% 47.52/47.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 47.52/47.79           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 47.52/47.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 47.52/47.79  thf('96', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['94', '95'])).
% 47.52/47.79  thf('97', plain,
% 47.52/47.79      (![X3 : $i, X4 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X3 @ X4)
% 47.52/47.79           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 47.52/47.79  thf('98', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 47.52/47.79           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['96', '97'])).
% 47.52/47.79  thf('99', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 47.52/47.79      inference('demod', [status(thm)], ['20', '21'])).
% 47.52/47.79  thf('100', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 47.52/47.79      inference('demod', [status(thm)], ['98', '99'])).
% 47.52/47.79  thf('101', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 47.52/47.79           = (X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['91', '100'])).
% 47.52/47.79  thf('102', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 47.52/47.79           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X0 @ X1)))
% 47.52/47.79           = (k5_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('sup+', [status(thm)], ['55', '101'])).
% 47.52/47.79  thf('103', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 47.52/47.79  thf('104', plain,
% 47.52/47.79      (![X12 : $i, X13 : $i, X14 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 47.52/47.79           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 47.52/47.79      inference('cnf', [status(esa)], [t49_xboole_1])).
% 47.52/47.79  thf('105', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 47.52/47.79           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 47.52/47.79      inference('sup+', [status(thm)], ['103', '104'])).
% 47.52/47.79  thf('106', plain,
% 47.52/47.79      (![X18 : $i, X19 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X18 @ X19)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 47.52/47.79              (k3_xboole_0 @ X18 @ X19)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t93_xboole_1])).
% 47.52/47.79  thf('107', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['81', '82'])).
% 47.52/47.79  thf('108', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0))
% 47.52/47.79           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['106', '107'])).
% 47.52/47.79  thf('109', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 47.52/47.79           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 47.52/47.79      inference('sup+', [status(thm)], ['103', '104'])).
% 47.52/47.79  thf('110', plain,
% 47.52/47.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 47.52/47.79           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t91_xboole_1])).
% 47.52/47.79  thf('111', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 47.52/47.79      inference('demod', [status(thm)], ['108', '109', '110'])).
% 47.52/47.79  thf('112', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['47', '48'])).
% 47.52/47.79  thf('113', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['39', '45'])).
% 47.52/47.79  thf('114', plain,
% 47.52/47.79      (![X18 : $i, X19 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X18 @ X19)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 47.52/47.79              (k3_xboole_0 @ X18 @ X19)))),
% 47.52/47.79      inference('cnf', [status(esa)], [t93_xboole_1])).
% 47.52/47.79  thf('115', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 47.52/47.79           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))))),
% 47.52/47.79      inference('sup+', [status(thm)], ['113', '114'])).
% 47.52/47.79  thf('116', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['112', '115'])).
% 47.52/47.79  thf('117', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['47', '48'])).
% 47.52/47.79  thf('118', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k2_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['52', '53'])).
% 47.52/47.79  thf('119', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['116', '117', '118'])).
% 47.52/47.79  thf('120', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['81', '82'])).
% 47.52/47.79  thf('121', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X1 @ X0)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['119', '120'])).
% 47.52/47.79  thf('122', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['14', '15'])).
% 47.52/47.79  thf('123', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('demod', [status(thm)], ['39', '45'])).
% 47.52/47.79  thf('124', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ X1)
% 47.52/47.79           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 47.52/47.79      inference('sup+', [status(thm)], ['122', '123'])).
% 47.52/47.79  thf('125', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))
% 47.52/47.79           = (k3_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['111', '121', '124'])).
% 47.52/47.79  thf('126', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]:
% 47.52/47.79         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 47.52/47.79           = (k5_xboole_0 @ X0 @ X1))),
% 47.52/47.79      inference('demod', [status(thm)], ['102', '105', '125'])).
% 47.52/47.79  thf('127', plain,
% 47.52/47.79      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 47.52/47.79      inference('sup+', [status(thm)], ['49', '50'])).
% 47.52/47.79  thf('128', plain,
% 47.52/47.79      (((k5_xboole_0 @ sk_A @ sk_B) != (k5_xboole_0 @ sk_A @ sk_B))),
% 47.52/47.79      inference('demod', [status(thm)], ['0', '126', '127'])).
% 47.52/47.79  thf('129', plain, ($false), inference('simplify', [status(thm)], ['128'])).
% 47.52/47.79  
% 47.52/47.79  % SZS output end Refutation
% 47.52/47.79  
% 47.52/47.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
