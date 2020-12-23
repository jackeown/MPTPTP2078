%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HOLaA2DkBK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 129 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  696 (1012 expanded)
%              Number of equality atoms :   43 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ( ( k7_relat_1 @ X26 @ X27 )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X20 @ ( k6_relat_1 @ X21 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X12 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B ) @ sk_B )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k9_relat_1 @ X15 @ ( k9_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ X1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X12 @ X14 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X2 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('51',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['28','52'])).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) @ X17 )
        = ( k9_relat_1 @ X15 @ ( k9_relat_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ sk_C ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_A @ sk_B )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HOLaA2DkBK
% 0.16/0.36  % Computer   : n021.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 17:00:35 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 1.51/1.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.72  % Solved by: fo/fo7.sh
% 1.51/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.72  % done 1922 iterations in 1.243s
% 1.51/1.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.72  % SZS output start Refutation
% 1.51/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.72  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.51/1.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.51/1.72  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.51/1.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.51/1.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.72  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.51/1.72  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.51/1.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.51/1.72  thf(t94_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.51/1.72  thf('0', plain,
% 1.51/1.72      (![X24 : $i, X25 : $i]:
% 1.51/1.72         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 1.51/1.72          | ~ (v1_relat_1 @ X25))),
% 1.51/1.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.51/1.72  thf(t71_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.51/1.72       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.51/1.72  thf('1', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf(t146_relat_1, axiom,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.51/1.72  thf('2', plain,
% 1.51/1.72      (![X9 : $i]:
% 1.51/1.72         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 1.51/1.72          | ~ (v1_relat_1 @ X9))),
% 1.51/1.72      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.51/1.72  thf('3', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 1.51/1.72            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.51/1.72      inference('sup+', [status(thm)], ['1', '2'])).
% 1.51/1.72  thf('4', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 1.51/1.72  thf('5', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('6', plain, (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.51/1.72  thf(t162_relat_1, conjecture,
% 1.51/1.72    (![A:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) =>
% 1.51/1.72       ( ![B:$i,C:$i]:
% 1.51/1.72         ( ( r1_tarski @ B @ C ) =>
% 1.51/1.72           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.51/1.72             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 1.51/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.72    (~( ![A:$i]:
% 1.51/1.72        ( ( v1_relat_1 @ A ) =>
% 1.51/1.72          ( ![B:$i,C:$i]:
% 1.51/1.72            ( ( r1_tarski @ B @ C ) =>
% 1.51/1.72              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 1.51/1.72                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 1.51/1.72    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 1.51/1.72  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('8', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf(t97_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.51/1.72         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.51/1.72  thf('9', plain,
% 1.51/1.72      (![X26 : $i, X27 : $i]:
% 1.51/1.72         (~ (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 1.51/1.72          | ((k7_relat_1 @ X26 @ X27) = (X26))
% 1.51/1.72          | ~ (v1_relat_1 @ X26))),
% 1.51/1.72      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.51/1.72  thf('10', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (r1_tarski @ X0 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.72          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['8', '9'])).
% 1.51/1.72  thf('11', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('12', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (r1_tarski @ X0 @ X1)
% 1.51/1.72          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 1.51/1.72      inference('demod', [status(thm)], ['10', '11'])).
% 1.51/1.72  thf('13', plain,
% 1.51/1.72      (((k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) = (k6_relat_1 @ sk_B))),
% 1.51/1.72      inference('sup-', [status(thm)], ['7', '12'])).
% 1.51/1.72  thf('14', plain,
% 1.51/1.72      (![X24 : $i, X25 : $i]:
% 1.51/1.72         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 1.51/1.72          | ~ (v1_relat_1 @ X25))),
% 1.51/1.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.51/1.72  thf(t76_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 1.51/1.72         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 1.51/1.72  thf('15', plain,
% 1.51/1.72      (![X20 : $i, X21 : $i]:
% 1.51/1.72         ((r1_tarski @ (k5_relat_1 @ X20 @ (k6_relat_1 @ X21)) @ X20)
% 1.51/1.72          | ~ (v1_relat_1 @ X20))),
% 1.51/1.72      inference('cnf', [status(esa)], [t76_relat_1])).
% 1.51/1.72  thf('16', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         ((r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.51/1.72           (k6_relat_1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.51/1.72      inference('sup+', [status(thm)], ['14', '15'])).
% 1.51/1.72  thf('17', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('18', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('19', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.51/1.72  thf('20', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_C))),
% 1.51/1.72      inference('sup+', [status(thm)], ['13', '19'])).
% 1.51/1.72  thf(t157_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ![C:$i]:
% 1.51/1.72         ( ( v1_relat_1 @ C ) =>
% 1.51/1.72           ( ( r1_tarski @ B @ C ) =>
% 1.51/1.72             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 1.51/1.72  thf('21', plain,
% 1.51/1.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X12)
% 1.51/1.72          | (r1_tarski @ (k9_relat_1 @ X13 @ X14) @ (k9_relat_1 @ X12 @ X14))
% 1.51/1.72          | ~ (r1_tarski @ X13 @ X12)
% 1.51/1.72          | ~ (v1_relat_1 @ X13))),
% 1.51/1.72      inference('cnf', [status(esa)], [t157_relat_1])).
% 1.51/1.72  thf('22', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 1.51/1.72          | (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 1.51/1.72             (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['20', '21'])).
% 1.51/1.72  thf('23', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('24', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('25', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ 
% 1.51/1.72          (k9_relat_1 @ (k6_relat_1 @ sk_C) @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.51/1.72  thf('26', plain,
% 1.51/1.72      ((r1_tarski @ sk_B @ (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B))),
% 1.51/1.72      inference('sup+', [status(thm)], ['6', '25'])).
% 1.51/1.72  thf(d10_xboole_0, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.72  thf('27', plain,
% 1.51/1.72      (![X0 : $i, X2 : $i]:
% 1.51/1.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.51/1.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.51/1.72  thf('28', plain,
% 1.51/1.72      ((~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) @ sk_B)
% 1.51/1.72        | ((k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) = (sk_B)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['26', '27'])).
% 1.51/1.72  thf('29', plain,
% 1.51/1.72      (![X24 : $i, X25 : $i]:
% 1.51/1.72         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 1.51/1.72          | ~ (v1_relat_1 @ X25))),
% 1.51/1.72      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.51/1.72  thf('30', plain,
% 1.51/1.72      (![X9 : $i]:
% 1.51/1.72         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 1.51/1.72          | ~ (v1_relat_1 @ X9))),
% 1.51/1.72      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.51/1.72  thf(t159_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ B ) =>
% 1.51/1.72       ( ![C:$i]:
% 1.51/1.72         ( ( v1_relat_1 @ C ) =>
% 1.51/1.72           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.51/1.72             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 1.51/1.72  thf('31', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X15)
% 1.51/1.72          | ((k9_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 1.51/1.72              = (k9_relat_1 @ X15 @ (k9_relat_1 @ X16 @ X17)))
% 1.51/1.72          | ~ (v1_relat_1 @ X16))),
% 1.51/1.72      inference('cnf', [status(esa)], [t159_relat_1])).
% 1.51/1.72  thf('32', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.51/1.72            = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0)))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X1))),
% 1.51/1.72      inference('sup+', [status(thm)], ['30', '31'])).
% 1.51/1.72  thf('33', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ((k9_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.51/1.72              = (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))),
% 1.51/1.72      inference('simplify', [status(thm)], ['32'])).
% 1.51/1.72  thf('34', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 1.51/1.72            (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.51/1.72            = (k9_relat_1 @ X1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 1.51/1.72          | ~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ X1))),
% 1.51/1.72      inference('sup+', [status(thm)], ['29', '33'])).
% 1.51/1.72  thf('35', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf('36', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 1.51/1.72      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.51/1.72  thf('37', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('38', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0) = (k9_relat_1 @ X1 @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ X1)
% 1.51/1.72          | ~ (v1_relat_1 @ X1))),
% 1.51/1.72      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.51/1.72  thf('39', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X1)
% 1.51/1.72          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 1.51/1.72              = (k9_relat_1 @ X1 @ X0)))),
% 1.51/1.72      inference('simplify', [status(thm)], ['38'])).
% 1.51/1.72  thf(dt_k7_relat_1, axiom,
% 1.51/1.72    (![A:$i,B:$i]:
% 1.51/1.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.51/1.72  thf('40', plain,
% 1.51/1.72      (![X7 : $i, X8 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.51/1.72  thf('41', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (r1_tarski @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ (k6_relat_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.51/1.72  thf('42', plain,
% 1.51/1.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X12)
% 1.51/1.72          | (r1_tarski @ (k9_relat_1 @ X13 @ X14) @ (k9_relat_1 @ X12 @ X14))
% 1.51/1.72          | ~ (r1_tarski @ X13 @ X12)
% 1.51/1.72          | ~ (v1_relat_1 @ X13))),
% 1.51/1.72      inference('cnf', [status(esa)], [t157_relat_1])).
% 1.51/1.72  thf('43', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.51/1.72          | (r1_tarski @ 
% 1.51/1.72             (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 1.51/1.72             (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['41', '42'])).
% 1.51/1.72  thf('44', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('45', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.51/1.72          | (r1_tarski @ 
% 1.51/1.72             (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 1.51/1.72             (k9_relat_1 @ (k6_relat_1 @ X0) @ X2)))),
% 1.51/1.72      inference('demod', [status(thm)], ['43', '44'])).
% 1.51/1.72  thf('46', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.51/1.72          | (r1_tarski @ 
% 1.51/1.72             (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 1.51/1.72             (k9_relat_1 @ (k6_relat_1 @ X0) @ X2)))),
% 1.51/1.72      inference('sup-', [status(thm)], ['40', '45'])).
% 1.51/1.72  thf('47', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('48', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.72         (r1_tarski @ 
% 1.51/1.72          (k9_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X2) @ 
% 1.51/1.72          (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))),
% 1.51/1.72      inference('demod', [status(thm)], ['46', '47'])).
% 1.51/1.72  thf('49', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         ((r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ 
% 1.51/1.72           (k9_relat_1 @ (k6_relat_1 @ X0) @ X0))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.51/1.72      inference('sup+', [status(thm)], ['39', '48'])).
% 1.51/1.72  thf('50', plain,
% 1.51/1.72      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.51/1.72  thf('51', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('52', plain,
% 1.51/1.72      (![X0 : $i, X1 : $i]:
% 1.51/1.72         (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.51/1.72      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.51/1.72  thf('53', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 1.51/1.72      inference('demod', [status(thm)], ['28', '52'])).
% 1.51/1.72  thf('54', plain,
% 1.51/1.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X15)
% 1.51/1.72          | ((k9_relat_1 @ (k5_relat_1 @ X16 @ X15) @ X17)
% 1.51/1.72              = (k9_relat_1 @ X15 @ (k9_relat_1 @ X16 @ X17)))
% 1.51/1.72          | ~ (v1_relat_1 @ X16))),
% 1.51/1.72      inference('cnf', [status(esa)], [t159_relat_1])).
% 1.51/1.72  thf('55', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 1.51/1.72            = (k9_relat_1 @ X0 @ sk_B))
% 1.51/1.72          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('sup+', [status(thm)], ['53', '54'])).
% 1.51/1.72  thf('56', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 1.51/1.72      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 1.51/1.72  thf('57', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_C) @ X0) @ sk_B)
% 1.51/1.72            = (k9_relat_1 @ X0 @ sk_B))
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('demod', [status(thm)], ['55', '56'])).
% 1.51/1.72  thf('58', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 1.51/1.72            = (k9_relat_1 @ X0 @ sk_B))
% 1.51/1.72          | ~ (v1_relat_1 @ X0)
% 1.51/1.72          | ~ (v1_relat_1 @ X0))),
% 1.51/1.72      inference('sup+', [status(thm)], ['0', '57'])).
% 1.51/1.72  thf('59', plain,
% 1.51/1.72      (![X0 : $i]:
% 1.51/1.72         (~ (v1_relat_1 @ X0)
% 1.51/1.72          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ sk_C) @ sk_B)
% 1.51/1.72              = (k9_relat_1 @ X0 @ sk_B)))),
% 1.51/1.72      inference('simplify', [status(thm)], ['58'])).
% 1.51/1.72  thf('60', plain,
% 1.51/1.72      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 1.51/1.72         != (k9_relat_1 @ sk_A @ sk_B))),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('61', plain,
% 1.51/1.72      ((((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))
% 1.51/1.72        | ~ (v1_relat_1 @ sk_A))),
% 1.51/1.72      inference('sup-', [status(thm)], ['59', '60'])).
% 1.51/1.72  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 1.51/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.72  thf('63', plain,
% 1.51/1.72      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 1.51/1.72      inference('demod', [status(thm)], ['61', '62'])).
% 1.51/1.72  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 1.51/1.72  
% 1.51/1.72  % SZS output end Refutation
% 1.51/1.72  
% 1.51/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
