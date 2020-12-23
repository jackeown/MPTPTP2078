%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZdOoQeYgRt

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:25 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 137 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  954 (1392 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X16 )
        = ( k7_relat_1 @ X14 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k7_relat_1 @ X18 @ X19 ) @ ( k7_relat_1 @ X17 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k2_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X24 @ X25 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t154_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_relat_1])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZdOoQeYgRt
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:32:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.65/1.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.84  % Solved by: fo/fo7.sh
% 1.65/1.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.84  % done 1193 iterations in 1.378s
% 1.65/1.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.84  % SZS output start Refutation
% 1.65/1.84  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.84  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.84  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.65/1.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.65/1.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.65/1.84  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.84  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.65/1.84  thf(t148_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ B ) =>
% 1.65/1.84       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.65/1.84  thf('0', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf(t70_enumset1, axiom,
% 1.65/1.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.65/1.84  thf('1', plain,
% 1.65/1.84      (![X3 : $i, X4 : $i]:
% 1.65/1.84         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 1.65/1.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.65/1.84  thf(t100_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i,C:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ C ) =>
% 1.65/1.84       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.65/1.84         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.65/1.84  thf('2', plain,
% 1.65/1.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.84         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.65/1.84            = (k7_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16)))
% 1.65/1.84          | ~ (v1_relat_1 @ X14))),
% 1.65/1.84      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.65/1.84  thf(t12_setfam_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.65/1.84  thf('3', plain,
% 1.65/1.84      (![X5 : $i, X6 : $i]:
% 1.65/1.84         ((k1_setfam_1 @ (k2_tarski @ X5 @ X6)) = (k3_xboole_0 @ X5 @ X6))),
% 1.65/1.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.84  thf('4', plain,
% 1.65/1.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.84         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.65/1.84            = (k7_relat_1 @ X14 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))
% 1.65/1.84          | ~ (v1_relat_1 @ X14))),
% 1.65/1.84      inference('demod', [status(thm)], ['2', '3'])).
% 1.65/1.84  thf('5', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf('6', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84            = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['4', '5'])).
% 1.65/1.84  thf('7', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84              = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['6'])).
% 1.65/1.84  thf('8', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf('9', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.65/1.84            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 1.65/1.84      inference('sup+', [status(thm)], ['7', '8'])).
% 1.65/1.84  thf(dt_k7_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.65/1.84  thf('10', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('11', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.65/1.84              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 1.65/1.84      inference('clc', [status(thm)], ['9', '10'])).
% 1.65/1.84  thf('12', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))
% 1.65/1.84            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['1', '11'])).
% 1.65/1.84  thf('13', plain,
% 1.65/1.84      (![X3 : $i, X4 : $i]:
% 1.65/1.84         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 1.65/1.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.65/1.84  thf('14', plain,
% 1.65/1.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.84         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.65/1.84            = (k7_relat_1 @ X14 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))
% 1.65/1.84          | ~ (v1_relat_1 @ X14))),
% 1.65/1.84      inference('demod', [status(thm)], ['2', '3'])).
% 1.65/1.84  thf('15', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 1.65/1.84            = (k7_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['13', '14'])).
% 1.65/1.84  thf('16', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf('17', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84            = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['15', '16'])).
% 1.65/1.84  thf('18', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84              = (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0)))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['17'])).
% 1.65/1.84  thf('19', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['12', '18'])).
% 1.65/1.84  thf('20', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ((k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['19'])).
% 1.65/1.84  thf('21', plain,
% 1.65/1.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.84         (((k7_relat_1 @ (k7_relat_1 @ X14 @ X15) @ X16)
% 1.65/1.84            = (k7_relat_1 @ X14 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16))))
% 1.65/1.84          | ~ (v1_relat_1 @ X14))),
% 1.65/1.84      inference('demod', [status(thm)], ['2', '3'])).
% 1.65/1.84  thf('22', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('23', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['21', '22'])).
% 1.65/1.84  thf('24', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['23'])).
% 1.65/1.84  thf(t88_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 1.65/1.84  thf('25', plain,
% 1.65/1.84      (![X24 : $i, X25 : $i]:
% 1.65/1.84         ((r1_tarski @ (k7_relat_1 @ X24 @ X25) @ X24) | ~ (v1_relat_1 @ X24))),
% 1.65/1.84      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.65/1.84  thf(t105_relat_1, axiom,
% 1.65/1.84    (![A:$i,B:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ B ) =>
% 1.65/1.84       ( ![C:$i]:
% 1.65/1.84         ( ( v1_relat_1 @ C ) =>
% 1.65/1.84           ( ( r1_tarski @ B @ C ) =>
% 1.65/1.84             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 1.65/1.84  thf('26', plain,
% 1.65/1.84      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X17)
% 1.65/1.84          | (r1_tarski @ (k7_relat_1 @ X18 @ X19) @ (k7_relat_1 @ X17 @ X19))
% 1.65/1.84          | ~ (r1_tarski @ X18 @ X17)
% 1.65/1.84          | ~ (v1_relat_1 @ X18))),
% 1.65/1.84      inference('cnf', [status(esa)], [t105_relat_1])).
% 1.65/1.84  thf('27', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.65/1.84          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 1.65/1.84             (k7_relat_1 @ X0 @ X2))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['25', '26'])).
% 1.65/1.84  thf('28', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 1.65/1.84           (k7_relat_1 @ X0 @ X2))
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['27'])).
% 1.65/1.84  thf('29', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('30', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 1.65/1.84             (k7_relat_1 @ X0 @ X2)))),
% 1.65/1.84      inference('clc', [status(thm)], ['28', '29'])).
% 1.65/1.84  thf(t25_relat_1, axiom,
% 1.65/1.84    (![A:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ A ) =>
% 1.65/1.84       ( ![B:$i]:
% 1.65/1.84         ( ( v1_relat_1 @ B ) =>
% 1.65/1.84           ( ( r1_tarski @ A @ B ) =>
% 1.65/1.84             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.65/1.84               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.65/1.84  thf('31', plain,
% 1.65/1.84      (![X22 : $i, X23 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X22)
% 1.65/1.84          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 1.65/1.84          | ~ (r1_tarski @ X23 @ X22)
% 1.65/1.84          | ~ (v1_relat_1 @ X23))),
% 1.65/1.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.65/1.84  thf('32', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 1.65/1.84          | (r1_tarski @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)) @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.65/1.84      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.84  thf('33', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 1.65/1.84          | (r1_tarski @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup-', [status(thm)], ['24', '32'])).
% 1.65/1.84  thf('34', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ 
% 1.65/1.84           (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 1.65/1.84           (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('simplify', [status(thm)], ['33'])).
% 1.65/1.84  thf('35', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('36', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | (r1_tarski @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)) @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 1.65/1.84      inference('clc', [status(thm)], ['34', '35'])).
% 1.65/1.84  thf('37', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 1.65/1.84           (k2_relat_1 @ (k7_relat_1 @ X2 @ X0)))
% 1.65/1.84          | ~ (v1_relat_1 @ X2)
% 1.65/1.84          | ~ (v1_relat_1 @ X2))),
% 1.65/1.84      inference('sup+', [status(thm)], ['20', '36'])).
% 1.65/1.84  thf('38', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 1.65/1.84             (k2_relat_1 @ (k7_relat_1 @ X2 @ X0))))),
% 1.65/1.84      inference('simplify', [status(thm)], ['37'])).
% 1.65/1.84  thf('39', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 1.65/1.84           (k9_relat_1 @ X1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['0', '38'])).
% 1.65/1.84  thf('40', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 1.65/1.84             (k9_relat_1 @ X1 @ X0)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['39'])).
% 1.65/1.84  thf('41', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf('42', plain,
% 1.65/1.84      (![X20 : $i, X21 : $i]:
% 1.65/1.84         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 1.65/1.84          | ~ (v1_relat_1 @ X20))),
% 1.65/1.84      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.65/1.84  thf('43', plain,
% 1.65/1.84      (![X24 : $i, X25 : $i]:
% 1.65/1.84         ((r1_tarski @ (k7_relat_1 @ X24 @ X25) @ X24) | ~ (v1_relat_1 @ X24))),
% 1.65/1.84      inference('cnf', [status(esa)], [t88_relat_1])).
% 1.65/1.84  thf('44', plain,
% 1.65/1.84      (![X22 : $i, X23 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X22)
% 1.65/1.84          | (r1_tarski @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22))
% 1.65/1.84          | ~ (r1_tarski @ X23 @ X22)
% 1.65/1.84          | ~ (v1_relat_1 @ X23))),
% 1.65/1.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.65/1.84  thf('45', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.65/1.84          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.65/1.84             (k2_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('sup-', [status(thm)], ['43', '44'])).
% 1.65/1.84  thf('46', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.65/1.84           (k2_relat_1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.65/1.84          | ~ (v1_relat_1 @ X0))),
% 1.65/1.84      inference('simplify', [status(thm)], ['45'])).
% 1.65/1.84  thf('47', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('48', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X0)
% 1.65/1.84          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 1.65/1.84             (k2_relat_1 @ X0)))),
% 1.65/1.84      inference('clc', [status(thm)], ['46', '47'])).
% 1.65/1.84  thf('49', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup+', [status(thm)], ['42', '48'])).
% 1.65/1.84  thf('50', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 1.65/1.84      inference('simplify', [status(thm)], ['49'])).
% 1.65/1.84  thf('51', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.65/1.84           (k9_relat_1 @ X1 @ X0))
% 1.65/1.84          | ~ (v1_relat_1 @ X1)
% 1.65/1.84          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.65/1.84      inference('sup+', [status(thm)], ['41', '50'])).
% 1.65/1.84  thf('52', plain,
% 1.65/1.84      (![X12 : $i, X13 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 1.65/1.84      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.65/1.84  thf('53', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.65/1.84             (k9_relat_1 @ X1 @ X0)))),
% 1.65/1.84      inference('clc', [status(thm)], ['51', '52'])).
% 1.65/1.84  thf(t19_xboole_1, axiom,
% 1.65/1.84    (![A:$i,B:$i,C:$i]:
% 1.65/1.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.65/1.84       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.65/1.84  thf('54', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (r1_tarski @ X0 @ X1)
% 1.65/1.84          | ~ (r1_tarski @ X0 @ X2)
% 1.65/1.84          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.65/1.84      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.65/1.84  thf('55', plain,
% 1.65/1.84      (![X5 : $i, X6 : $i]:
% 1.65/1.84         ((k1_setfam_1 @ (k2_tarski @ X5 @ X6)) = (k3_xboole_0 @ X5 @ X6))),
% 1.65/1.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.84  thf('56', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (r1_tarski @ X0 @ X1)
% 1.65/1.84          | ~ (r1_tarski @ X0 @ X2)
% 1.65/1.84          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X2))))),
% 1.65/1.84      inference('demod', [status(thm)], ['54', '55'])).
% 1.65/1.84  thf('57', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 1.65/1.84             (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X3)))
% 1.65/1.84          | ~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ X3))),
% 1.65/1.84      inference('sup-', [status(thm)], ['53', '56'])).
% 1.65/1.84  thf('58', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X1)
% 1.65/1.84          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 1.65/1.84             (k1_setfam_1 @ 
% 1.65/1.84              (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('sup-', [status(thm)], ['40', '57'])).
% 1.65/1.84  thf('59', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 1.65/1.84           (k1_setfam_1 @ 
% 1.65/1.84            (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 1.65/1.84          | ~ (v1_relat_1 @ X1))),
% 1.65/1.84      inference('simplify', [status(thm)], ['58'])).
% 1.65/1.84  thf('60', plain,
% 1.65/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.84         (~ (v1_relat_1 @ X2)
% 1.65/1.84          | ((k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.65/1.84              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 1.65/1.84      inference('clc', [status(thm)], ['9', '10'])).
% 1.65/1.84  thf(t154_relat_1, conjecture,
% 1.65/1.84    (![A:$i,B:$i,C:$i]:
% 1.65/1.84     ( ( v1_relat_1 @ C ) =>
% 1.65/1.84       ( r1_tarski @
% 1.65/1.84         ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.65/1.84         ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.65/1.84  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.84    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.84        ( ( v1_relat_1 @ C ) =>
% 1.65/1.84          ( r1_tarski @
% 1.65/1.84            ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.65/1.84            ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 1.65/1.84    inference('cnf.neg', [status(esa)], [t154_relat_1])).
% 1.65/1.84  thf('61', plain,
% 1.65/1.84      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.65/1.84          (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 1.65/1.84           (k9_relat_1 @ sk_C @ sk_B)))),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('62', plain,
% 1.65/1.84      (![X5 : $i, X6 : $i]:
% 1.65/1.84         ((k1_setfam_1 @ (k2_tarski @ X5 @ X6)) = (k3_xboole_0 @ X5 @ X6))),
% 1.65/1.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.84  thf('63', plain,
% 1.65/1.84      (![X5 : $i, X6 : $i]:
% 1.65/1.84         ((k1_setfam_1 @ (k2_tarski @ X5 @ X6)) = (k3_xboole_0 @ X5 @ X6))),
% 1.65/1.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.65/1.84  thf('64', plain,
% 1.65/1.84      (~ (r1_tarski @ 
% 1.65/1.84          (k9_relat_1 @ sk_C @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 1.65/1.84          (k1_setfam_1 @ 
% 1.65/1.84           (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.65/1.84  thf('65', plain,
% 1.65/1.84      ((~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 1.65/1.84           (k1_setfam_1 @ 
% 1.65/1.84            (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 1.65/1.84             (k9_relat_1 @ sk_C @ sk_B))))
% 1.65/1.84        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.84      inference('sup-', [status(thm)], ['60', '64'])).
% 1.65/1.84  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('67', plain,
% 1.65/1.84      (~ (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 1.65/1.84          (k1_setfam_1 @ 
% 1.65/1.84           (k2_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))))),
% 1.65/1.84      inference('demod', [status(thm)], ['65', '66'])).
% 1.65/1.84  thf('68', plain, (~ (v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('sup-', [status(thm)], ['59', '67'])).
% 1.65/1.84  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.84  thf('70', plain, ($false), inference('demod', [status(thm)], ['68', '69'])).
% 1.65/1.84  
% 1.65/1.84  % SZS output end Refutation
% 1.65/1.84  
% 1.65/1.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
