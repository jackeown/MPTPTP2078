%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qLMRubINAG

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:48 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 180 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          :  801 (1720 expanded)
%              Number of equality atoms :   43 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ ( k9_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X12 @ X10 ) @ ( k10_relat_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k10_relat_1 @ X14 @ ( k10_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k9_relat_1 @ X6 @ ( k9_relat_1 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('18',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('28',plain,
    ( ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_A )
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,
    ( ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_A )
    = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','39','40','41'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('44',plain,
    ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('46',plain,
    ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['14','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('50',plain,
    ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','50'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('52',plain,(
    ! [X28: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k10_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X26 ) @ X27 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('57',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['51','58','59','60'])).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( r1_tarski @ ( k10_relat_1 @ X24 @ ( k9_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('63',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('66',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('67',plain,(
    ! [X21: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('68',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('69',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['12','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qLMRubINAG
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 152 iterations in 0.110s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.61  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.61  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(t157_funct_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.61       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.41/0.61           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.61         ( r1_tarski @ A @ B ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.41/0.61          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.41/0.61              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.61            ( r1_tarski @ A @ B ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.41/0.61  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t152_funct_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.61       ( ( v2_funct_1 @ B ) =>
% 0.41/0.61         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (v2_funct_1 @ X24)
% 0.41/0.61          | (r1_tarski @ (k10_relat_1 @ X24 @ (k9_relat_1 @ X24 @ X25)) @ X25)
% 0.41/0.61          | ~ (v1_funct_1 @ X24)
% 0.41/0.61          | ~ (v1_relat_1 @ X24))),
% 0.41/0.61      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t178_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ( r1_tarski @ A @ B ) =>
% 0.41/0.61         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X10 @ X11)
% 0.41/0.61          | ~ (v1_relat_1 @ X12)
% 0.41/0.61          | (r1_tarski @ (k10_relat_1 @ X12 @ X10) @ (k10_relat_1 @ X12 @ X11)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.41/0.61           (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.41/0.61          | ~ (v1_relat_1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf(t1_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.61       ( r1_tarski @ A @ C ) ))).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.41/0.61          | (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X0)
% 0.41/0.61          | (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ X1)
% 0.41/0.61          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)) @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.61        | (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '6'])).
% 0.41/0.61  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.41/0.61  thf(t181_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( v1_relat_1 @ C ) =>
% 0.41/0.61           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.41/0.61             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X13)
% 0.41/0.61          | ((k10_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 0.41/0.61              = (k10_relat_1 @ X14 @ (k10_relat_1 @ X13 @ X15)))
% 0.41/0.61          | ~ (v1_relat_1 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.41/0.61  thf(dt_k5_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.41/0.61       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X3)
% 0.41/0.61          | ~ (v1_relat_1 @ X4)
% 0.41/0.61          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.41/0.61  thf(t159_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( v1_relat_1 @ C ) =>
% 0.41/0.61           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.41/0.61             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X6)
% 0.41/0.61          | ((k9_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 0.41/0.61              = (k9_relat_1 @ X6 @ (k9_relat_1 @ X7 @ X8)))
% 0.41/0.61          | ~ (v1_relat_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X3)
% 0.41/0.61          | ~ (v1_relat_1 @ X4)
% 0.41/0.61          | (v1_relat_1 @ (k5_relat_1 @ X3 @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.41/0.61  thf('17', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t71_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.41/0.61       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.61  thf('18', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.61  thf(t46_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( v1_relat_1 @ B ) =>
% 0.41/0.61           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.61             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X16)
% 0.41/0.61          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) = (k1_relat_1 @ X17))
% 0.41/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.41/0.61          | ~ (v1_relat_1 @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.41/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.61          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.61              = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.41/0.61          | ~ (v1_relat_1 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf(fc3_funct_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.61  thf('21', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('22', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 0.41/0.61          | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X0))
% 0.41/0.61          | ~ (v1_relat_1 @ X1))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)) = (sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '23'])).
% 0.41/0.61  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)) = (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf(t146_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X5 : $i]:
% 0.41/0.61         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.41/0.61          | ~ (v1_relat_1 @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      ((((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_A)
% 0.41/0.61          = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))
% 0.41/0.61        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['26', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_A)
% 0.41/0.61            = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '28'])).
% 0.41/0.61  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('31', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((k9_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_A)
% 0.41/0.61         = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.41/0.61      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      ((((k9_relat_1 @ sk_C @ (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A))
% 0.41/0.61          = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))
% 0.41/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.61      inference('sup+', [status(thm)], ['15', '32'])).
% 0.41/0.61  thf('34', plain, (![X18 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 0.41/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X5 : $i]:
% 0.41/0.61         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.41/0.61          | ~ (v1_relat_1 @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.41/0.61            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.41/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.61  thf('37', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.61  thf('38', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.41/0.61  thf('40', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (((k9_relat_1 @ sk_C @ sk_A)
% 0.41/0.61         = (k2_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.41/0.61      inference('demod', [status(thm)], ['33', '39', '40', '41'])).
% 0.41/0.61  thf(t169_relat_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ A ) =>
% 0.41/0.61       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (![X9 : $i]:
% 0.41/0.61         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.41/0.61          | ~ (v1_relat_1 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      ((((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.41/0.61          (k9_relat_1 @ sk_C @ sk_A))
% 0.41/0.61          = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))
% 0.41/0.61        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)) = (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      ((((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.41/0.61          (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)))),
% 0.41/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.41/0.61            (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['14', '46'])).
% 0.41/0.61  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('49', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.41/0.61         (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      ((((k10_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.41/0.61          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))) = (sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.41/0.61      inference('sup+', [status(thm)], ['13', '50'])).
% 0.41/0.61  thf(t67_funct_1, axiom,
% 0.41/0.61    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      (![X28 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X28)) = (k6_relat_1 @ X28))),
% 0.41/0.61      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.41/0.61  thf(t155_funct_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.61       ( ( v2_funct_1 @ B ) =>
% 0.41/0.61         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (![X26 : $i, X27 : $i]:
% 0.41/0.61         (~ (v2_funct_1 @ X26)
% 0.41/0.61          | ((k10_relat_1 @ X26 @ X27)
% 0.41/0.61              = (k9_relat_1 @ (k2_funct_1 @ X26) @ X27))
% 0.41/0.61          | ~ (v1_funct_1 @ X26)
% 0.41/0.61          | ~ (v1_relat_1 @ X26))),
% 0.41/0.61      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.41/0.61            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.41/0.61          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.41/0.61          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.41/0.61          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.41/0.61  thf('55', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('56', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf(fc4_funct_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.41/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.41/0.61  thf('57', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.41/0.61           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.41/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.41/0.61  thf('59', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.41/0.61         (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))) = (sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['51', '58', '59', '60'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (v2_funct_1 @ X24)
% 0.41/0.61          | (r1_tarski @ (k10_relat_1 @ X24 @ (k9_relat_1 @ X24 @ X25)) @ X25)
% 0.41/0.61          | ~ (v1_funct_1 @ X24)
% 0.41/0.61          | ~ (v1_relat_1 @ X24))),
% 0.41/0.61      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_A) @ 
% 0.41/0.61         (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.41/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 0.41/0.61        | ~ (v2_funct_1 @ (k6_relat_1 @ sk_A)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['61', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.41/0.61           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.41/0.61      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.41/0.61  thf('66', plain, (![X20 : $i]: (v1_relat_1 @ (k6_relat_1 @ X20))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('67', plain, (![X21 : $i]: (v1_funct_1 @ (k6_relat_1 @ X21))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.41/0.61  thf('68', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['63', '64', '65', '66', '67', '68'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.41/0.61          | (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ sk_A @ X0)
% 0.41/0.61          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.41/0.61               X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.61  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['12', '71'])).
% 0.41/0.61  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
