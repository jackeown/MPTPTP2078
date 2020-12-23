%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SSJ262aRFd

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:40 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   69 (  78 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  673 ( 783 expanded)
%              Number of equality atoms :   43 (  51 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k9_relat_1 @ X4 @ X5 )
        = ( k9_relat_1 @ X4 @ ( k3_xboole_0 @ ( k1_relat_1 @ X4 ) @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ X23 @ ( k2_funct_1 @ X23 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k10_relat_1 @ X9 @ ( k10_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X6 @ X7 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) ) @ X0 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','18'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ ( k6_relat_1 @ X20 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t154_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( ( k9_relat_1 @ B @ A )
            = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t154_funct_1])).

thf('34',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k9_relat_1 @ sk_B @ sk_A )
 != ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SSJ262aRFd
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.58/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.84  % Solved by: fo/fo7.sh
% 0.58/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.84  % done 398 iterations in 0.363s
% 0.58/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.84  % SZS output start Refutation
% 0.58/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.84  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.58/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.58/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.58/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.84  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.58/0.84  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.58/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.84  thf('0', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.84  thf(t145_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ( k9_relat_1 @ B @ A ) =
% 0.58/0.84         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.58/0.84  thf('1', plain,
% 0.58/0.84      (![X4 : $i, X5 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X4 @ X5)
% 0.58/0.84            = (k9_relat_1 @ X4 @ (k3_xboole_0 @ (k1_relat_1 @ X4) @ X5)))
% 0.58/0.84          | ~ (v1_relat_1 @ X4))),
% 0.58/0.84      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.58/0.84  thf('2', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X0 @ X1)
% 0.58/0.84            = (k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0))))
% 0.58/0.84          | ~ (v1_relat_1 @ X0))),
% 0.58/0.84      inference('sup+', [status(thm)], ['0', '1'])).
% 0.58/0.84  thf(t61_funct_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.84       ( ( v2_funct_1 @ A ) =>
% 0.58/0.84         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.58/0.84             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.58/0.84           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.58/0.84             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.84  thf('3', plain,
% 0.58/0.84      (![X23 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X23)
% 0.58/0.84          | ((k5_relat_1 @ X23 @ (k2_funct_1 @ X23))
% 0.58/0.84              = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 0.58/0.84          | ~ (v1_funct_1 @ X23)
% 0.58/0.84          | ~ (v1_relat_1 @ X23))),
% 0.58/0.84      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.58/0.84  thf(dt_k2_funct_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.84       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.58/0.84         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.58/0.84  thf('4', plain,
% 0.58/0.84      (![X15 : $i]:
% 0.58/0.84         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.58/0.84          | ~ (v1_funct_1 @ X15)
% 0.58/0.84          | ~ (v1_relat_1 @ X15))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.84  thf(t181_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( ![C:$i]:
% 0.58/0.84         ( ( v1_relat_1 @ C ) =>
% 0.58/0.84           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.58/0.84             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.58/0.84  thf('5', plain,
% 0.58/0.84      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X8)
% 0.58/0.84          | ((k10_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.58/0.84              = (k10_relat_1 @ X9 @ (k10_relat_1 @ X8 @ X10)))
% 0.58/0.84          | ~ (v1_relat_1 @ X9))),
% 0.58/0.84      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.58/0.84  thf('6', plain,
% 0.58/0.84      (![X15 : $i]:
% 0.58/0.84         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.58/0.84          | ~ (v1_funct_1 @ X15)
% 0.58/0.84          | ~ (v1_relat_1 @ X15))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.58/0.84  thf(t55_funct_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.84       ( ( v2_funct_1 @ A ) =>
% 0.58/0.84         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.58/0.84           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.58/0.84  thf('7', plain,
% 0.58/0.84      (![X22 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X22)
% 0.58/0.84          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 0.58/0.84          | ~ (v1_funct_1 @ X22)
% 0.58/0.84          | ~ (v1_relat_1 @ X22))),
% 0.58/0.84      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.58/0.84  thf(t167_relat_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ B ) =>
% 0.58/0.84       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.58/0.84  thf('8', plain,
% 0.58/0.84      (![X6 : $i, X7 : $i]:
% 0.58/0.84         ((r1_tarski @ (k10_relat_1 @ X6 @ X7) @ (k1_relat_1 @ X6))
% 0.58/0.84          | ~ (v1_relat_1 @ X6))),
% 0.58/0.84      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.58/0.84  thf('9', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 0.58/0.84           (k2_relat_1 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['7', '8'])).
% 0.58/0.84  thf('10', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 0.58/0.84             (k2_relat_1 @ X0)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['6', '9'])).
% 0.58/0.84  thf('11', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 0.58/0.84           (k2_relat_1 @ X0))
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.84  thf(t147_funct_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.84       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.58/0.84         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.58/0.84  thf('12', plain,
% 0.58/0.84      (![X18 : $i, X19 : $i]:
% 0.58/0.84         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 0.58/0.84          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 0.58/0.84          | ~ (v1_funct_1 @ X19)
% 0.58/0.84          | ~ (v1_relat_1 @ X19))),
% 0.58/0.84      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.58/0.84  thf('13', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ((k9_relat_1 @ X0 @ 
% 0.58/0.84              (k10_relat_1 @ X0 @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.58/0.84              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.58/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.84  thf('14', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X0 @ 
% 0.58/0.84            (k10_relat_1 @ X0 @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 0.58/0.84            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['13'])).
% 0.58/0.84  thf('15', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X1 @ 
% 0.58/0.84            (k10_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0))
% 0.58/0.84            = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_funct_1 @ X1)
% 0.58/0.84          | ~ (v2_funct_1 @ X1))),
% 0.58/0.84      inference('sup+', [status(thm)], ['5', '14'])).
% 0.58/0.84  thf('16', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X1)
% 0.58/0.84          | ~ (v1_funct_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ((k9_relat_1 @ X1 @ 
% 0.58/0.84              (k10_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X1)) @ X0))
% 0.58/0.84              = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['15'])).
% 0.58/0.84  thf('17', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ((k9_relat_1 @ X0 @ 
% 0.58/0.84              (k10_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1))
% 0.58/0.84              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0))),
% 0.58/0.84      inference('sup-', [status(thm)], ['4', '16'])).
% 0.58/0.84  thf('18', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X0)
% 0.58/0.84          | ((k9_relat_1 @ X0 @ 
% 0.58/0.84              (k10_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)) @ X1))
% 0.58/0.84              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0))),
% 0.58/0.84      inference('simplify', [status(thm)], ['17'])).
% 0.58/0.84  thf('19', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X0 @ 
% 0.58/0.84            (k10_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X1))
% 0.58/0.84            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0))),
% 0.58/0.84      inference('sup+', [status(thm)], ['3', '18'])).
% 0.58/0.84  thf(t43_funct_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.58/0.84       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.84  thf('20', plain,
% 0.58/0.84      (![X20 : $i, X21 : $i]:
% 0.58/0.84         ((k5_relat_1 @ (k6_relat_1 @ X21) @ (k6_relat_1 @ X20))
% 0.58/0.84           = (k6_relat_1 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.58/0.84      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.58/0.84  thf(t71_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.58/0.84       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.58/0.84  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf(t182_relat_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v1_relat_1 @ A ) =>
% 0.58/0.84       ( ![B:$i]:
% 0.58/0.84         ( ( v1_relat_1 @ B ) =>
% 0.58/0.84           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.58/0.84             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.58/0.84  thf('22', plain,
% 0.58/0.84      (![X11 : $i, X12 : $i]:
% 0.58/0.84         (~ (v1_relat_1 @ X11)
% 0.58/0.84          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.58/0.84              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.58/0.84          | ~ (v1_relat_1 @ X12))),
% 0.58/0.84      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.58/0.84  thf('23', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.84            = (k10_relat_1 @ X1 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['21', '22'])).
% 0.58/0.84  thf(fc4_funct_1, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.58/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.58/0.84  thf('24', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.58/0.84  thf('25', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.58/0.84            = (k10_relat_1 @ X1 @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X1))),
% 0.58/0.84      inference('demod', [status(thm)], ['23', '24'])).
% 0.58/0.84  thf('26', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.58/0.84            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.58/0.84      inference('sup+', [status(thm)], ['20', '25'])).
% 0.58/0.84  thf('27', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.58/0.84      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.58/0.84  thf('28', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.58/0.84      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.58/0.84  thf('29', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((k3_xboole_0 @ X1 @ X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.58/0.84      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.58/0.84  thf('30', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.58/0.84            = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v2_funct_1 @ X0))),
% 0.58/0.84      inference('demod', [status(thm)], ['19', '29'])).
% 0.58/0.84  thf('31', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_funct_1 @ X0)
% 0.58/0.84          | ~ (v1_relat_1 @ X0)
% 0.58/0.84          | ((k9_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.58/0.84              = (k10_relat_1 @ (k2_funct_1 @ X0) @ X1)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.84  thf('32', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (((k9_relat_1 @ X1 @ X0) = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0))
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ~ (v1_funct_1 @ X1)
% 0.58/0.84          | ~ (v2_funct_1 @ X1))),
% 0.58/0.84      inference('sup+', [status(thm)], ['2', '31'])).
% 0.58/0.84  thf('33', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         (~ (v2_funct_1 @ X1)
% 0.58/0.84          | ~ (v1_funct_1 @ X1)
% 0.58/0.84          | ~ (v1_relat_1 @ X1)
% 0.58/0.84          | ((k9_relat_1 @ X1 @ X0) = (k10_relat_1 @ (k2_funct_1 @ X1) @ X0)))),
% 0.58/0.84      inference('simplify', [status(thm)], ['32'])).
% 0.58/0.84  thf(t154_funct_1, conjecture,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.84       ( ( v2_funct_1 @ B ) =>
% 0.58/0.84         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.84    (~( ![A:$i,B:$i]:
% 0.58/0.84        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.84          ( ( v2_funct_1 @ B ) =>
% 0.58/0.84            ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )),
% 0.58/0.84    inference('cnf.neg', [status(esa)], [t154_funct_1])).
% 0.58/0.84  thf('34', plain,
% 0.58/0.84      (((k9_relat_1 @ sk_B @ sk_A)
% 0.58/0.84         != (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('35', plain,
% 0.58/0.84      ((((k9_relat_1 @ sk_B @ sk_A) != (k9_relat_1 @ sk_B @ sk_A))
% 0.58/0.84        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.84        | ~ (v1_funct_1 @ sk_B)
% 0.58/0.84        | ~ (v2_funct_1 @ sk_B))),
% 0.58/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.84  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.84  thf('39', plain,
% 0.58/0.84      (((k9_relat_1 @ sk_B @ sk_A) != (k9_relat_1 @ sk_B @ sk_A))),
% 0.58/0.84      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.58/0.84  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.58/0.84  
% 0.58/0.84  % SZS output end Refutation
% 0.58/0.84  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
