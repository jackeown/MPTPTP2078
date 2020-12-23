%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4bSsVwe2MV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:32 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 145 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  744 (1061 expanded)
%              Number of equality atoms :   80 ( 124 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X56 @ X57 ) @ X58 )
        = ( k7_relat_1 @ X56 @ ( k3_xboole_0 @ X57 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X56 @ X57 ) @ X58 )
        = ( k7_relat_1 @ X56 @ ( k1_setfam_1 @ ( k2_tarski @ X57 @ X58 ) ) ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X59 @ X60 ) ) @ ( k1_relat_1 @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('4',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X61 ) @ X62 )
      | ( ( k7_relat_1 @ X61 @ X62 )
        = X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X54 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('10',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ o_0_0_xboole_0 )
      = X16 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['28','29','42'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k6_subset_1 @ X50 @ X51 )
      = ( k4_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('46',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('51',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k6_subset_1 @ X50 @ X51 )
      = ( k4_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k6_subset_1 @ X50 @ X51 )
      = ( k4_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X9 @ X10 ) @ X10 )
      = ( k6_subset_1 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['48','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','21','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['12','61'])).

thf('63',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4bSsVwe2MV
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.06  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.06  % Solved by: fo/fo7.sh
% 0.84/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.06  % done 1031 iterations in 0.582s
% 0.84/1.06  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.06  % SZS output start Refutation
% 0.84/1.06  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.84/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.06  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.84/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.06  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.84/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.84/1.06  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.84/1.06  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.84/1.06  thf(t100_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ C ) =>
% 0.84/1.06       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.84/1.06         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.84/1.06  thf('0', plain,
% 0.84/1.06      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.84/1.06         (((k7_relat_1 @ (k7_relat_1 @ X56 @ X57) @ X58)
% 0.84/1.06            = (k7_relat_1 @ X56 @ (k3_xboole_0 @ X57 @ X58)))
% 0.84/1.06          | ~ (v1_relat_1 @ X56))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.84/1.06  thf(t12_setfam_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.84/1.06  thf('1', plain,
% 0.84/1.06      (![X52 : $i, X53 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.06  thf('2', plain,
% 0.84/1.06      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.84/1.06         (((k7_relat_1 @ (k7_relat_1 @ X56 @ X57) @ X58)
% 0.84/1.06            = (k7_relat_1 @ X56 @ (k1_setfam_1 @ (k2_tarski @ X57 @ X58))))
% 0.84/1.06          | ~ (v1_relat_1 @ X56))),
% 0.84/1.06      inference('demod', [status(thm)], ['0', '1'])).
% 0.84/1.06  thf(t89_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ B ) =>
% 0.84/1.06       ( r1_tarski @
% 0.84/1.06         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.84/1.06  thf('3', plain,
% 0.84/1.06      (![X59 : $i, X60 : $i]:
% 0.84/1.06         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X59 @ X60)) @ 
% 0.84/1.06           (k1_relat_1 @ X59))
% 0.84/1.06          | ~ (v1_relat_1 @ X59))),
% 0.84/1.06      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.84/1.06  thf(t97_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ B ) =>
% 0.84/1.06       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.84/1.06         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.84/1.06  thf('4', plain,
% 0.84/1.06      (![X61 : $i, X62 : $i]:
% 0.84/1.06         (~ (r1_tarski @ (k1_relat_1 @ X61) @ X62)
% 0.84/1.06          | ((k7_relat_1 @ X61 @ X62) = (X61))
% 0.84/1.06          | ~ (v1_relat_1 @ X61))),
% 0.84/1.06      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.84/1.06  thf('5', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ X0)
% 0.84/1.06          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.84/1.06          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.84/1.06              = (k7_relat_1 @ X0 @ X1)))),
% 0.84/1.06      inference('sup-', [status(thm)], ['3', '4'])).
% 0.84/1.06  thf(dt_k7_relat_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.84/1.06  thf('6', plain,
% 0.84/1.06      (![X54 : $i, X55 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ X54) | (v1_relat_1 @ (k7_relat_1 @ X54 @ X55)))),
% 0.84/1.06      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.84/1.06  thf('7', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.84/1.06            = (k7_relat_1 @ X0 @ X1))
% 0.84/1.06          | ~ (v1_relat_1 @ X0))),
% 0.84/1.06      inference('clc', [status(thm)], ['5', '6'])).
% 0.84/1.06  thf('8', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (((k7_relat_1 @ X0 @ 
% 0.84/1.06            (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0))))
% 0.84/1.06            = (k7_relat_1 @ X0 @ X1))
% 0.84/1.06          | ~ (v1_relat_1 @ X0)
% 0.84/1.06          | ~ (v1_relat_1 @ X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['2', '7'])).
% 0.84/1.06  thf('9', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         (~ (v1_relat_1 @ X0)
% 0.84/1.06          | ((k7_relat_1 @ X0 @ 
% 0.84/1.06              (k1_setfam_1 @ (k2_tarski @ X1 @ (k1_relat_1 @ X0))))
% 0.84/1.06              = (k7_relat_1 @ X0 @ X1)))),
% 0.84/1.06      inference('simplify', [status(thm)], ['8'])).
% 0.84/1.06  thf(t192_relat_1, conjecture,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( v1_relat_1 @ B ) =>
% 0.84/1.06       ( ( k7_relat_1 @ B @ A ) =
% 0.84/1.06         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.84/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.06    (~( ![A:$i,B:$i]:
% 0.84/1.06        ( ( v1_relat_1 @ B ) =>
% 0.84/1.06          ( ( k7_relat_1 @ B @ A ) =
% 0.84/1.06            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.84/1.06    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.84/1.06  thf('10', plain,
% 0.84/1.06      (((k7_relat_1 @ sk_B @ sk_A)
% 0.84/1.06         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('11', plain,
% 0.84/1.06      (![X52 : $i, X53 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.06  thf('12', plain,
% 0.84/1.06      (((k7_relat_1 @ sk_B @ sk_A)
% 0.84/1.06         != (k7_relat_1 @ sk_B @ 
% 0.84/1.06             (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.84/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.84/1.06  thf(commutativity_k5_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('13', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf(t95_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k3_xboole_0 @ A @ B ) =
% 0.84/1.06       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('14', plain,
% 0.84/1.06      (![X21 : $i, X22 : $i]:
% 0.84/1.06         ((k3_xboole_0 @ X21 @ X22)
% 0.84/1.06           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.84/1.06              (k2_xboole_0 @ X21 @ X22)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.84/1.06  thf('15', plain,
% 0.84/1.06      (![X52 : $i, X53 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.06  thf('16', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('17', plain,
% 0.84/1.06      (![X21 : $i, X22 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22))
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.84/1.06              (k5_xboole_0 @ X21 @ X22)))),
% 0.84/1.06      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.84/1.06  thf('18', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['13', '17'])).
% 0.84/1.06  thf(t91_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.06       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.84/1.06  thf('19', plain,
% 0.84/1.06      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.84/1.06           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.06  thf('20', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('21', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.84/1.06           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['19', '20'])).
% 0.84/1.06  thf(idempotence_k2_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.84/1.06  thf('22', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.84/1.06      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.84/1.06  thf(t4_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i,C:$i]:
% 0.84/1.06     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.06       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.84/1.06  thf('23', plain,
% 0.84/1.06      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.84/1.06         ((k2_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X15)
% 0.84/1.06           = (k2_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.84/1.06  thf('24', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k2_xboole_0 @ X0 @ X1)
% 0.84/1.06           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['22', '23'])).
% 0.84/1.06  thf(commutativity_k2_xboole_0, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.84/1.06  thf('25', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.06  thf('26', plain,
% 0.84/1.06      (![X21 : $i, X22 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22))
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ 
% 0.84/1.06              (k5_xboole_0 @ X21 @ X22)))),
% 0.84/1.06      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.84/1.06  thf('27', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['25', '26'])).
% 0.84/1.06  thf('28', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 0.84/1.06              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['24', '27'])).
% 0.84/1.06  thf('29', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('30', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf(t92_xboole_1, axiom,
% 0.84/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.84/1.06  thf('31', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.06  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.84/1.06  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.84/1.06  thf('33', plain,
% 0.84/1.06      (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (o_0_0_xboole_0))),
% 0.84/1.06      inference('demod', [status(thm)], ['31', '32'])).
% 0.84/1.06  thf('34', plain,
% 0.84/1.06      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.84/1.06           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.06  thf('35', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k5_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.84/1.06           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['33', '34'])).
% 0.84/1.06  thf('36', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf(t5_boole, axiom,
% 0.84/1.06    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.84/1.06  thf('37', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.84/1.06      inference('cnf', [status(esa)], [t5_boole])).
% 0.84/1.06  thf('38', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.84/1.06      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.84/1.06  thf('39', plain,
% 0.84/1.06      (![X16 : $i]: ((k5_xboole_0 @ X16 @ o_0_0_xboole_0) = (X16))),
% 0.84/1.06      inference('demod', [status(thm)], ['37', '38'])).
% 0.84/1.06  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ o_0_0_xboole_0 @ X0) = (X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['36', '39'])).
% 0.84/1.06  thf('41', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['35', '40'])).
% 0.84/1.06  thf('42', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['30', '41'])).
% 0.84/1.06  thf('43', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 0.84/1.06      inference('demod', [status(thm)], ['28', '29', '42'])).
% 0.84/1.06  thf(t100_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.06  thf('44', plain,
% 0.84/1.06      (![X5 : $i, X6 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ X5 @ X6)
% 0.84/1.06           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.84/1.06      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.06  thf(redefinition_k6_subset_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.06  thf('45', plain,
% 0.84/1.06      (![X50 : $i, X51 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.06  thf('46', plain,
% 0.84/1.06      (![X52 : $i, X53 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 0.84/1.06      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.84/1.06  thf('47', plain,
% 0.84/1.06      (![X5 : $i, X6 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X5 @ X6)
% 0.84/1.06           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 0.84/1.06      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.84/1.06  thf('48', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.84/1.06           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.84/1.06      inference('sup+', [status(thm)], ['43', '47'])).
% 0.84/1.06  thf('49', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.84/1.06  thf(t40_xboole_1, axiom,
% 0.84/1.06    (![A:$i,B:$i]:
% 0.84/1.06     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.84/1.06  thf('50', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i]:
% 0.84/1.06         ((k4_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.84/1.06           = (k4_xboole_0 @ X9 @ X10))),
% 0.84/1.06      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.84/1.06  thf('51', plain,
% 0.84/1.06      (![X50 : $i, X51 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.06  thf('52', plain,
% 0.84/1.06      (![X50 : $i, X51 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X50 @ X51) = (k4_xboole_0 @ X50 @ X51))),
% 0.84/1.06      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.84/1.06  thf('53', plain,
% 0.84/1.06      (![X9 : $i, X10 : $i]:
% 0.84/1.06         ((k6_subset_1 @ (k2_xboole_0 @ X9 @ X10) @ X10)
% 0.84/1.06           = (k6_subset_1 @ X9 @ X10))),
% 0.84/1.06      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.84/1.06  thf('54', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.84/1.06           = (k6_subset_1 @ X0 @ X1))),
% 0.84/1.06      inference('sup+', [status(thm)], ['49', '53'])).
% 0.84/1.06  thf('55', plain,
% 0.84/1.06      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.84/1.06      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.06  thf('56', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X1 @ X0)
% 0.84/1.06           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.84/1.06      inference('demod', [status(thm)], ['48', '54', '55'])).
% 0.84/1.06  thf('57', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 0.84/1.06           = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['18', '21', '56'])).
% 0.84/1.06  thf('58', plain,
% 0.84/1.06      (![X5 : $i, X6 : $i]:
% 0.84/1.06         ((k6_subset_1 @ X5 @ X6)
% 0.84/1.06           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 0.84/1.06      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.84/1.06  thf('59', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.06      inference('demod', [status(thm)], ['35', '40'])).
% 0.84/1.06  thf('60', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.84/1.06           = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['58', '59'])).
% 0.84/1.06  thf('61', plain,
% 0.84/1.06      (![X0 : $i, X1 : $i]:
% 0.84/1.06         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 0.84/1.06           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.84/1.06      inference('sup+', [status(thm)], ['57', '60'])).
% 0.84/1.06  thf('62', plain,
% 0.84/1.06      (((k7_relat_1 @ sk_B @ sk_A)
% 0.84/1.06         != (k7_relat_1 @ sk_B @ 
% 0.84/1.06             (k1_setfam_1 @ (k2_tarski @ sk_A @ (k1_relat_1 @ sk_B)))))),
% 0.84/1.06      inference('demod', [status(thm)], ['12', '61'])).
% 0.84/1.06  thf('63', plain,
% 0.84/1.06      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.84/1.06        | ~ (v1_relat_1 @ sk_B))),
% 0.84/1.06      inference('sup-', [status(thm)], ['9', '62'])).
% 0.84/1.06  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.84/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.06  thf('65', plain,
% 0.84/1.06      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.84/1.06      inference('demod', [status(thm)], ['63', '64'])).
% 0.84/1.06  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.84/1.06  
% 0.84/1.06  % SZS output end Refutation
% 0.84/1.06  
% 0.84/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
