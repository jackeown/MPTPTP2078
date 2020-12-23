%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fqmjOwGD63

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:30 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 174 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  690 (1246 expanded)
%              Number of equality atoms :   66 ( 113 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','19'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['24','42'])).

thf('44',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','47'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('62',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ X25 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('69',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( sk_A
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('78',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['48','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fqmjOwGD63
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.89  % Solved by: fo/fo7.sh
% 0.66/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.89  % done 956 iterations in 0.439s
% 0.66/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.89  % SZS output start Refutation
% 0.66/0.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.89  thf(t106_xboole_1, conjecture,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.66/0.89       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.66/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.89        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.66/0.89          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.66/0.89    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.66/0.89  thf('0', plain,
% 0.66/0.89      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('1', plain,
% 0.66/0.89      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.89  thf('2', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.89  thf(t100_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.89  thf('3', plain,
% 0.66/0.89      (![X10 : $i, X11 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X10 @ X11)
% 0.66/0.89           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.89  thf('4', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.89           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['2', '3'])).
% 0.66/0.89  thf('5', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.89  thf(l97_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.66/0.89  thf('6', plain,
% 0.66/0.89      (![X8 : $i, X9 : $i]:
% 0.66/0.89         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.66/0.89      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.66/0.89  thf('7', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('sup+', [status(thm)], ['5', '6'])).
% 0.66/0.89  thf('8', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X1) @ 
% 0.66/0.89          (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['4', '7'])).
% 0.66/0.89  thf(t16_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.89       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.66/0.89  thf('9', plain,
% 0.66/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.89           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.89  thf(idempotence_k3_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.66/0.89  thf('10', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.66/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.89  thf('11', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))),
% 0.66/0.89      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.66/0.89  thf(d7_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.66/0.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.89  thf('12', plain,
% 0.66/0.89      (![X4 : $i, X5 : $i]:
% 0.66/0.89         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.66/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.66/0.89  thf('13', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.89           = (k1_xboole_0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.89  thf('14', plain,
% 0.66/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.89           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.89  thf(t36_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.66/0.89  thf('15', plain,
% 0.66/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.66/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.89  thf(t28_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.89  thf('16', plain,
% 0.66/0.89      (![X15 : $i, X16 : $i]:
% 0.66/0.89         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.66/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.89  thf('17', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.66/0.89           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.89  thf('18', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.89  thf('19', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.89           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.89  thf('20', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.66/0.89      inference('demod', [status(thm)], ['13', '14', '19'])).
% 0.66/0.89  thf('21', plain,
% 0.66/0.89      (![X10 : $i, X11 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X10 @ X11)
% 0.66/0.89           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.89  thf('22', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.89           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['20', '21'])).
% 0.66/0.89  thf(t5_boole, axiom,
% 0.66/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.89  thf('23', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.66/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.89  thf('24', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.66/0.89      inference('demod', [status(thm)], ['22', '23'])).
% 0.66/0.89  thf('25', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.66/0.89      inference('demod', [status(thm)], ['13', '14', '19'])).
% 0.66/0.89  thf('26', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('27', plain,
% 0.66/0.89      (![X15 : $i, X16 : $i]:
% 0.66/0.89         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.66/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.89  thf('28', plain,
% 0.66/0.89      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.89  thf('29', plain,
% 0.66/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.89           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.89  thf('30', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ sk_A @ X0)
% 0.66/0.89           = (k3_xboole_0 @ sk_A @ 
% 0.66/0.89              (k3_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C) @ X0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['28', '29'])).
% 0.66/0.89  thf('31', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ sk_A @ 
% 0.66/0.89           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.66/0.89           = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['25', '30'])).
% 0.66/0.89  thf('32', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.66/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.89  thf('33', plain,
% 0.66/0.89      (![X8 : $i, X9 : $i]:
% 0.66/0.89         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.66/0.89      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.66/0.89  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['32', '33'])).
% 0.66/0.89  thf(t92_xboole_1, axiom,
% 0.66/0.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.89  thf('35', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.66/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.66/0.89  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.66/0.89      inference('demod', [status(thm)], ['34', '35'])).
% 0.66/0.89  thf('37', plain,
% 0.66/0.89      (![X4 : $i, X5 : $i]:
% 0.66/0.89         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.66/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.66/0.89  thf('38', plain,
% 0.66/0.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.66/0.89  thf('39', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ sk_A @ 
% 0.66/0.89           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))) = (k1_xboole_0))),
% 0.66/0.89      inference('demod', [status(thm)], ['31', '38'])).
% 0.66/0.89  thf('40', plain,
% 0.66/0.89      (![X4 : $i, X6 : $i]:
% 0.66/0.89         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.66/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.66/0.89  thf('41', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.89          | (r1_xboole_0 @ sk_A @ 
% 0.66/0.89             (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.66/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.89  thf('42', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.66/0.89      inference('simplify', [status(thm)], ['41'])).
% 0.66/0.89  thf('43', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.66/0.89      inference('sup+', [status(thm)], ['24', '42'])).
% 0.66/0.89  thf('44', plain,
% 0.66/0.89      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('45', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.66/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.66/0.89  thf('46', plain,
% 0.66/0.89      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.66/0.89      inference('split', [status(esa)], ['0'])).
% 0.66/0.89  thf('47', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.66/0.89      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.66/0.89  thf('48', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.66/0.89      inference('simpl_trail', [status(thm)], ['1', '47'])).
% 0.66/0.89  thf('49', plain,
% 0.66/0.89      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.89  thf(t49_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.66/0.89       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.66/0.89  thf('50', plain,
% 0.66/0.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.66/0.89           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 0.66/0.89      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.66/0.89  thf('51', plain,
% 0.66/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.66/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.89  thf('52', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.66/0.89          (k3_xboole_0 @ X2 @ X1))),
% 0.66/0.89      inference('sup+', [status(thm)], ['50', '51'])).
% 0.66/0.89  thf('53', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.66/0.89      inference('sup+', [status(thm)], ['49', '52'])).
% 0.66/0.89  thf('54', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.89  thf('55', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['53', '54'])).
% 0.66/0.89  thf('56', plain,
% 0.66/0.89      (![X15 : $i, X16 : $i]:
% 0.66/0.89         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 0.66/0.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.89  thf('57', plain,
% 0.66/0.89      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['55', '56'])).
% 0.66/0.89  thf('58', plain,
% 0.66/0.89      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 0.66/0.89           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.66/0.89  thf('59', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.89  thf('60', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.66/0.89           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['58', '59'])).
% 0.66/0.89  thf('61', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.66/0.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.89  thf('62', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.66/0.89      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.66/0.89  thf('63', plain,
% 0.66/0.89      (![X10 : $i, X11 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X10 @ X11)
% 0.66/0.89           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.89  thf('64', plain,
% 0.66/0.89      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.66/0.89      inference('sup+', [status(thm)], ['62', '63'])).
% 0.66/0.89  thf('65', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.66/0.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.66/0.89  thf(t91_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.89       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.89  thf('66', plain,
% 0.66/0.89      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.66/0.89         ((k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ X25)
% 0.66/0.89           = (k5_xboole_0 @ X23 @ (k5_xboole_0 @ X24 @ X25)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.89  thf('67', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.66/0.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['65', '66'])).
% 0.66/0.89  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.89  thf('68', plain,
% 0.66/0.89      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.89  thf('69', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.66/0.89      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.89  thf('70', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['68', '69'])).
% 0.66/0.89  thf('71', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.89      inference('demod', [status(thm)], ['67', '70'])).
% 0.66/0.89  thf('72', plain,
% 0.66/0.89      (((sk_A) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['64', '71'])).
% 0.66/0.89  thf('73', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.66/0.89           = (k4_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.89  thf('74', plain,
% 0.66/0.89      (![X10 : $i, X11 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X10 @ X11)
% 0.66/0.89           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.66/0.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.89  thf('75', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.66/0.89           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.66/0.89      inference('sup+', [status(thm)], ['73', '74'])).
% 0.66/0.89  thf('76', plain,
% 0.66/0.89      (((sk_A) = (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.66/0.89      inference('demod', [status(thm)], ['72', '75'])).
% 0.66/0.89  thf('77', plain,
% 0.66/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.66/0.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.89  thf('78', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.66/0.89      inference('sup+', [status(thm)], ['76', '77'])).
% 0.66/0.89  thf('79', plain, ($false), inference('demod', [status(thm)], ['48', '78'])).
% 0.66/0.89  
% 0.66/0.89  % SZS output end Refutation
% 0.66/0.89  
% 0.66/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
