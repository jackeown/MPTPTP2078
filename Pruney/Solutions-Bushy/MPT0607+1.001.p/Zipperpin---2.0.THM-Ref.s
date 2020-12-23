%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0607+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4aMFPW9VP8

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:11 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   24 (  30 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  153 ( 255 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t211_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
         => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
            = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t211_relat_1])).

thf('0',plain,(
    ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) )
 != ( k7_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k7_relat_1 @ X3 @ X4 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf(t109_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k6_subset_1 @ X1 @ X2 ) )
        = ( k6_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t109_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
        = ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
      = ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k7_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
 != ( k7_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).


%------------------------------------------------------------------------------
