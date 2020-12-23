%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d65zmXNKoo

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 134 expanded)
%              Number of leaves         :   38 (  54 expanded)
%              Depth                    :   21
%              Number of atoms          :  774 (1057 expanded)
%              Number of equality atoms :   58 (  66 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) )
        = ( k10_relat_1 @ X25 @ ( k1_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X29: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k8_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X31: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X27 ) @ ( k4_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k7_relat_1 @ X33 @ X32 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ X33 ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k9_relat_1 @ X20 @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_A
    = ( k5_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,
    ( sk_A
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf(t163_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 ) @ ( k9_relat_1 @ ( k4_relat_1 @ X22 ) @ ( k9_relat_1 @ X22 @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t163_relat_1])).

thf('51',plain,
    ( ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k7_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d65zmXNKoo
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:35:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 136 iterations in 0.072s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.51  thf(t146_funct_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.51         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i]:
% 0.19/0.51        ( ( v1_relat_1 @ B ) =>
% 0.19/0.51          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.51            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t123_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.19/0.51          | ~ (v1_relat_1 @ X18))),
% 0.19/0.51      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.51  thf(t182_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( v1_relat_1 @ B ) =>
% 0.19/0.51           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.51             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X24 : $i, X25 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X24)
% 0.19/0.51          | ((k1_relat_1 @ (k5_relat_1 @ X25 @ X24))
% 0.19/0.51              = (k10_relat_1 @ X25 @ (k1_relat_1 @ X24)))
% 0.19/0.51          | ~ (v1_relat_1 @ X25))),
% 0.19/0.51      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.51            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X1))))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf(t71_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.51  thf('4', plain, (![X29 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 0.19/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.51  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.19/0.51  thf('5', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.51  thf(dt_k8_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         ((v1_relat_1 @ (k8_relat_1 @ X16 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.51  thf(t37_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.19/0.51         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      (![X26 : $i]:
% 0.19/0.51         (((k1_relat_1 @ X26) = (k2_relat_1 @ (k4_relat_1 @ X26)))
% 0.19/0.51          | ~ (v1_relat_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (((k8_relat_1 @ X19 @ X18) = (k5_relat_1 @ X18 @ (k6_relat_1 @ X19)))
% 0.19/0.51          | ~ (v1_relat_1 @ X18))),
% 0.19/0.51      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.19/0.51  thf(t72_relat_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X31 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X31)) = (k6_relat_1 @ X31))),
% 0.19/0.51      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.19/0.51  thf(t54_relat_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( v1_relat_1 @ B ) =>
% 0.19/0.51           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.51             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X27 : $i, X28 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X27)
% 0.19/0.51          | ((k4_relat_1 @ (k5_relat_1 @ X28 @ X27))
% 0.19/0.51              = (k5_relat_1 @ (k4_relat_1 @ X27) @ (k4_relat_1 @ X28)))
% 0.19/0.51          | ~ (v1_relat_1 @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.51  thf('14', plain, (![X15 : $i]: (v1_relat_1 @ (k6_relat_1 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.51            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.19/0.51          | ~ (v1_relat_1 @ X1))),
% 0.19/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf(t94_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X32 : $i, X33 : $i]:
% 0.19/0.51         (((k7_relat_1 @ X33 @ X32) = (k5_relat_1 @ (k6_relat_1 @ X32) @ X33))
% 0.19/0.51          | ~ (v1_relat_1 @ X33))),
% 0.19/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k4_relat_1 @ X1) @ X0)
% 0.19/0.51            = (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.19/0.51          | ~ (v1_relat_1 @ X1)
% 0.19/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf(dt_k4_relat_1, axiom,
% 0.19/0.51    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X14 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X1)
% 0.19/0.51          | ((k7_relat_1 @ (k4_relat_1 @ X1) @ X0)
% 0.19/0.51              = (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 0.19/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k7_relat_1 @ (k4_relat_1 @ X0) @ X1)
% 0.19/0.51            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.19/0.51          | ~ (v1_relat_1 @ X0)
% 0.19/0.51          | ~ (v1_relat_1 @ X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['10', '19'])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (~ (v1_relat_1 @ X0)
% 0.19/0.51          | ((k7_relat_1 @ (k4_relat_1 @ X0) @ X1)
% 0.19/0.51              = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X14 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.19/0.51  thf(t148_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (((k2_relat_1 @ (k7_relat_1 @ X20 @ X21)) = (k9_relat_1 @ X20 @ X21))
% 0.19/0.51          | ~ (v1_relat_1 @ X20))),
% 0.19/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.51  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(l32_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X2 : $i, X4 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.19/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (((k4_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.51  thf(t98_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i]:
% 0.19/0.51         ((k2_xboole_0 @ X12 @ X13)
% 0.19/0.51           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.51         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf(t5_boole, axiom,
% 0.19/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.51  thf('31', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.19/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.51  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (((k2_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.19/0.51  thf(t95_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k3_xboole_0 @ A @ B ) =
% 0.19/0.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.19/0.51           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.19/0.51              (k2_xboole_0 @ X10 @ X11)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.19/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.19/0.51              (k5_xboole_0 @ X10 @ X11)))),
% 0.19/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.51         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.51            (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['33', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.19/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.19/0.51         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.51            (k5_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.19/0.51  thf('40', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t12_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]:
% 0.19/0.51         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (((k2_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.19/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.19/0.51              (k5_xboole_0 @ X10 @ X11)))),
% 0.19/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.19/0.51         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.51            (k5_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('sup+', [status(thm)], ['42', '43'])).
% 0.19/0.51  thf('45', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t28_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.51  thf('47', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B)) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.51  thf('48', plain,
% 0.19/0.51      (((sk_A)
% 0.19/0.51         = (k5_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.19/0.51            (k5_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.19/0.51      inference('demod', [status(thm)], ['44', '47'])).
% 0.19/0.51  thf('49', plain, (((sk_A) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.19/0.51      inference('sup+', [status(thm)], ['39', '48'])).
% 0.19/0.51  thf(t163_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( r1_tarski @
% 0.19/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ 
% 0.19/0.51         ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ))).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i]:
% 0.19/0.51         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X22) @ X23) @ 
% 0.19/0.51           (k9_relat_1 @ (k4_relat_1 @ X22) @ (k9_relat_1 @ X22 @ X23)))
% 0.19/0.51          | ~ (v1_relat_1 @ X22))),
% 0.19/0.51      inference('cnf', [status(esa)], [t163_relat_1])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (((r1_tarski @ sk_A @ 
% 0.19/0.51         (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.19/0.51  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      ((r1_tarski @ sk_A @ 
% 0.19/0.51        (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['51', '52'])).
% 0.19/0.51  thf('54', plain,
% 0.19/0.51      (((r1_tarski @ sk_A @ 
% 0.19/0.51         (k2_relat_1 @ 
% 0.19/0.51          (k7_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.19/0.51        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_B)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['23', '53'])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.51        | (r1_tarski @ sk_A @ 
% 0.19/0.51           (k2_relat_1 @ 
% 0.19/0.51            (k7_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['22', '54'])).
% 0.19/0.51  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      ((r1_tarski @ sk_A @ 
% 0.19/0.51        (k2_relat_1 @ 
% 0.19/0.51         (k7_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (((r1_tarski @ sk_A @ 
% 0.19/0.51         (k2_relat_1 @ 
% 0.19/0.51          (k4_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['21', '57'])).
% 0.19/0.51  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      ((r1_tarski @ sk_A @ 
% 0.19/0.51        (k2_relat_1 @ 
% 0.19/0.51         (k4_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))),
% 0.19/0.51      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.51  thf('61', plain,
% 0.19/0.51      (((r1_tarski @ sk_A @ 
% 0.19/0.51         (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))
% 0.19/0.51        | ~ (v1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['9', '60'])).
% 0.19/0.51  thf('62', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.51        | (r1_tarski @ sk_A @ 
% 0.19/0.51           (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '61'])).
% 0.19/0.51  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      ((r1_tarski @ sk_A @ 
% 0.19/0.51        (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.19/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.19/0.51        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['7', '64'])).
% 0.19/0.51  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.19/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.19/0.51  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.33/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
