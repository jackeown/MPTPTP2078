%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeWAwFmnSB

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:10 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 118 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   24
%              Number of atoms          :  733 (1276 expanded)
%              Number of equality atoms :   43 (  74 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k10_relat_1 @ X4 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zeWAwFmnSB
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.94/2.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.12  % Solved by: fo/fo7.sh
% 1.94/2.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.12  % done 1978 iterations in 1.674s
% 1.94/2.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.12  % SZS output start Refutation
% 1.94/2.12  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.94/2.12  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.94/2.12  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.94/2.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.94/2.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.94/2.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.94/2.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.94/2.12  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.12  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.94/2.12  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.12  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.94/2.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.94/2.12  thf(t154_funct_1, axiom,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.12       ( ( v2_funct_1 @ B ) =>
% 1.94/2.12         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.94/2.12  thf('0', plain,
% 1.94/2.12      (![X14 : $i, X15 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X14)
% 1.94/2.12          | ((k9_relat_1 @ X14 @ X15)
% 1.94/2.12              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 1.94/2.12          | ~ (v1_funct_1 @ X14)
% 1.94/2.12          | ~ (v1_relat_1 @ X14))),
% 1.94/2.12      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.94/2.12  thf(t155_funct_1, axiom,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.12       ( ( v2_funct_1 @ B ) =>
% 1.94/2.12         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.94/2.12  thf('1', plain,
% 1.94/2.12      (![X16 : $i, X17 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X16)
% 1.94/2.12          | ((k10_relat_1 @ X16 @ X17)
% 1.94/2.12              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 1.94/2.12          | ~ (v1_funct_1 @ X16)
% 1.94/2.12          | ~ (v1_relat_1 @ X16))),
% 1.94/2.12      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.94/2.12  thf(dt_k2_funct_1, axiom,
% 1.94/2.12    (![A:$i]:
% 1.94/2.12     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.94/2.12       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.94/2.12         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.94/2.12  thf('2', plain,
% 1.94/2.12      (![X9 : $i]:
% 1.94/2.12         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.94/2.12          | ~ (v1_funct_1 @ X9)
% 1.94/2.12          | ~ (v1_relat_1 @ X9))),
% 1.94/2.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.94/2.12  thf('3', plain,
% 1.94/2.12      (![X9 : $i]:
% 1.94/2.12         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 1.94/2.12          | ~ (v1_funct_1 @ X9)
% 1.94/2.12          | ~ (v1_relat_1 @ X9))),
% 1.94/2.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.94/2.12  thf(t164_funct_1, conjecture,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.12       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.94/2.12         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.94/2.12  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.12    (~( ![A:$i,B:$i]:
% 1.94/2.12        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.12          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 1.94/2.12            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 1.94/2.12    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 1.94/2.12  thf('4', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 1.94/2.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.12  thf(t146_relat_1, axiom,
% 1.94/2.12    (![A:$i]:
% 1.94/2.12     ( ( v1_relat_1 @ A ) =>
% 1.94/2.12       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.94/2.12  thf('5', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.94/2.12  thf('6', plain,
% 1.94/2.12      (![X9 : $i]:
% 1.94/2.12         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.94/2.12          | ~ (v1_funct_1 @ X9)
% 1.94/2.12          | ~ (v1_relat_1 @ X9))),
% 1.94/2.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.94/2.12  thf('7', plain,
% 1.94/2.12      (![X14 : $i, X15 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X14)
% 1.94/2.12          | ((k9_relat_1 @ X14 @ X15)
% 1.94/2.12              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 1.94/2.12          | ~ (v1_funct_1 @ X14)
% 1.94/2.12          | ~ (v1_relat_1 @ X14))),
% 1.94/2.12      inference('cnf', [status(esa)], [t154_funct_1])).
% 1.94/2.12  thf(t167_relat_1, axiom,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( v1_relat_1 @ B ) =>
% 1.94/2.12       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.94/2.12  thf('8', plain,
% 1.94/2.12      (![X1 : $i, X2 : $i]:
% 1.94/2.12         ((r1_tarski @ (k10_relat_1 @ X1 @ X2) @ (k1_relat_1 @ X1))
% 1.94/2.12          | ~ (v1_relat_1 @ X1))),
% 1.94/2.12      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.94/2.12  thf('9', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 1.94/2.12           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 1.94/2.12          | ~ (v1_relat_1 @ X1)
% 1.94/2.12          | ~ (v1_funct_1 @ X1)
% 1.94/2.12          | ~ (v2_funct_1 @ X1)
% 1.94/2.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 1.94/2.12      inference('sup+', [status(thm)], ['7', '8'])).
% 1.94/2.12  thf('10', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         (~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 1.94/2.12             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.94/2.12      inference('sup-', [status(thm)], ['6', '9'])).
% 1.94/2.12  thf('11', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 1.94/2.12           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('simplify', [status(thm)], ['10'])).
% 1.94/2.12  thf('12', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0))),
% 1.94/2.12      inference('sup+', [status(thm)], ['5', '11'])).
% 1.94/2.12  thf('13', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 1.94/2.12      inference('simplify', [status(thm)], ['12'])).
% 1.94/2.12  thf(t79_relat_1, axiom,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( v1_relat_1 @ B ) =>
% 1.94/2.12       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.94/2.12         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.94/2.12  thf('14', plain,
% 1.94/2.12      (![X7 : $i, X8 : $i]:
% 1.94/2.12         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.94/2.12          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 1.94/2.12          | ~ (v1_relat_1 @ X7))),
% 1.94/2.12      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.94/2.12  thf('15', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.94/2.12              = (X0)))),
% 1.94/2.12      inference('sup-', [status(thm)], ['13', '14'])).
% 1.94/2.12  thf('16', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.94/2.12            = (X0))
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('simplify', [status(thm)], ['15'])).
% 1.94/2.12  thf(t71_relat_1, axiom,
% 1.94/2.12    (![A:$i]:
% 1.94/2.12     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.94/2.12       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.94/2.12  thf('17', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 1.94/2.12      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.94/2.12  thf(t182_relat_1, axiom,
% 1.94/2.12    (![A:$i]:
% 1.94/2.12     ( ( v1_relat_1 @ A ) =>
% 1.94/2.12       ( ![B:$i]:
% 1.94/2.12         ( ( v1_relat_1 @ B ) =>
% 1.94/2.12           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.94/2.12             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.94/2.12  thf('18', plain,
% 1.94/2.12      (![X3 : $i, X4 : $i]:
% 1.94/2.12         (~ (v1_relat_1 @ X3)
% 1.94/2.12          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 1.94/2.12              = (k10_relat_1 @ X4 @ (k1_relat_1 @ X3)))
% 1.94/2.12          | ~ (v1_relat_1 @ X4))),
% 1.94/2.12      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.94/2.12  thf('19', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.94/2.12            = (k10_relat_1 @ X1 @ X0))
% 1.94/2.12          | ~ (v1_relat_1 @ X1)
% 1.94/2.12          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.94/2.12      inference('sup+', [status(thm)], ['17', '18'])).
% 1.94/2.12  thf(fc3_funct_1, axiom,
% 1.94/2.12    (![A:$i]:
% 1.94/2.12     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.94/2.12       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.94/2.12  thf('20', plain, (![X10 : $i]: (v1_relat_1 @ (k6_relat_1 @ X10))),
% 1.94/2.12      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.94/2.12  thf('21', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 1.94/2.12            = (k10_relat_1 @ X1 @ X0))
% 1.94/2.12          | ~ (v1_relat_1 @ X1))),
% 1.94/2.12      inference('demod', [status(thm)], ['19', '20'])).
% 1.94/2.12  thf('22', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k1_relat_1 @ X0)
% 1.94/2.12            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('sup+', [status(thm)], ['16', '21'])).
% 1.94/2.12  thf('23', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ((k1_relat_1 @ X0)
% 1.94/2.12              = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 1.94/2.12      inference('simplify', [status(thm)], ['22'])).
% 1.94/2.12  thf('24', plain,
% 1.94/2.12      (![X9 : $i]:
% 1.94/2.12         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 1.94/2.12          | ~ (v1_funct_1 @ X9)
% 1.94/2.12          | ~ (v1_relat_1 @ X9))),
% 1.94/2.12      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.94/2.12  thf('25', plain,
% 1.94/2.12      (![X16 : $i, X17 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X16)
% 1.94/2.12          | ((k10_relat_1 @ X16 @ X17)
% 1.94/2.12              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 1.94/2.12          | ~ (v1_funct_1 @ X16)
% 1.94/2.12          | ~ (v1_relat_1 @ X16))),
% 1.94/2.12      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.94/2.12  thf('26', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.94/2.12  thf('27', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.94/2.12      inference('sup+', [status(thm)], ['25', '26'])).
% 1.94/2.12  thf('28', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.94/2.12      inference('sup-', [status(thm)], ['24', '27'])).
% 1.94/2.12  thf('29', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0))),
% 1.94/2.12      inference('simplify', [status(thm)], ['28'])).
% 1.94/2.12  thf('30', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0))),
% 1.94/2.12      inference('sup+', [status(thm)], ['23', '29'])).
% 1.94/2.12  thf('31', plain,
% 1.94/2.12      (![X0 : $i]:
% 1.94/2.12         (~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 1.94/2.12      inference('simplify', [status(thm)], ['30'])).
% 1.94/2.12  thf(t147_funct_1, axiom,
% 1.94/2.12    (![A:$i,B:$i]:
% 1.94/2.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.94/2.12       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.94/2.12         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.94/2.12  thf('32', plain,
% 1.94/2.12      (![X12 : $i, X13 : $i]:
% 1.94/2.12         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 1.94/2.12          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 1.94/2.12          | ~ (v1_funct_1 @ X13)
% 1.94/2.12          | ~ (v1_relat_1 @ X13))),
% 1.94/2.12      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.94/2.12  thf('33', plain,
% 1.94/2.12      (![X0 : $i, X1 : $i]:
% 1.94/2.12         (~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 1.94/2.12          | ~ (v1_relat_1 @ X0)
% 1.94/2.12          | ~ (v1_funct_1 @ X0)
% 1.94/2.12          | ~ (v2_funct_1 @ X0)
% 1.94/2.12          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.94/2.12          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.94/2.12          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.94/2.12              (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)) = (X1)))),
% 1.94/2.12      inference('sup-', [status(thm)], ['31', '32'])).
% 1.94/2.12  thf('34', plain,
% 1.94/2.12      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.12          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))
% 1.94/2.12        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.94/2.12        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.94/2.12        | ~ (v2_funct_1 @ sk_B)
% 1.94/2.12        | ~ (v1_funct_1 @ sk_B)
% 1.94/2.12        | ~ (v1_relat_1 @ sk_B))),
% 1.94/2.13      inference('sup-', [status(thm)], ['4', '33'])).
% 1.94/2.13  thf('35', plain, ((v2_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('38', plain,
% 1.94/2.13      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.13          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))
% 1.94/2.13        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 1.94/2.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 1.94/2.13      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.94/2.13  thf('39', plain,
% 1.94/2.13      ((~ (v1_relat_1 @ sk_B)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.94/2.13        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.94/2.13        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.13            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['3', '38'])).
% 1.94/2.13  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('42', plain,
% 1.94/2.13      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 1.94/2.13        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.13            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 1.94/2.13      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.94/2.13  thf('43', plain,
% 1.94/2.13      ((~ (v1_relat_1 @ sk_B)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.94/2.13        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.13            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 1.94/2.13      inference('sup-', [status(thm)], ['2', '42'])).
% 1.94/2.13  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('46', plain,
% 1.94/2.13      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 1.94/2.13         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))),
% 1.94/2.13      inference('demod', [status(thm)], ['43', '44', '45'])).
% 1.94/2.13  thf('47', plain,
% 1.94/2.13      ((((k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 1.94/2.13          = (sk_A))
% 1.94/2.13        | ~ (v1_relat_1 @ sk_B)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.94/2.13        | ~ (v2_funct_1 @ sk_B))),
% 1.94/2.13      inference('sup+', [status(thm)], ['1', '46'])).
% 1.94/2.13  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('50', plain, ((v2_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('51', plain,
% 1.94/2.13      (((k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 1.94/2.13         = (sk_A))),
% 1.94/2.13      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 1.94/2.13  thf('52', plain,
% 1.94/2.13      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 1.94/2.13        | ~ (v1_relat_1 @ sk_B)
% 1.94/2.13        | ~ (v1_funct_1 @ sk_B)
% 1.94/2.13        | ~ (v2_funct_1 @ sk_B))),
% 1.94/2.13      inference('sup+', [status(thm)], ['0', '51'])).
% 1.94/2.13  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('55', plain, ((v2_funct_1 @ sk_B)),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('56', plain,
% 1.94/2.13      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 1.94/2.13      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 1.94/2.13  thf('57', plain,
% 1.94/2.13      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 1.94/2.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.13  thf('58', plain, ($false),
% 1.94/2.13      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 1.94/2.13  
% 1.94/2.13  % SZS output end Refutation
% 1.94/2.13  
% 1.97/2.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
