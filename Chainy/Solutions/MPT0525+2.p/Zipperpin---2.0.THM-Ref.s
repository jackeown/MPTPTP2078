%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0525+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qEAPa0aEbb

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 11.86s
% Output     : Refutation 11.86s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 172 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_14_type,type,(
    sk_B_14: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ ( A @ B ) )
        = ( k5_relat_1 @ ( B @ ( k6_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X2194: $i,X2195: $i] :
      ( ( ( k8_relat_1 @ ( X2195 @ X2194 ) )
        = ( k5_relat_1 @ ( X2194 @ ( k6_relat_1 @ X2195 ) ) ) )
      | ~ ( v1_relat_1 @ X2194 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t125_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B @ A ) )
       => ( ( k8_relat_1 @ ( A @ B ) )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k2_relat_1 @ B @ A ) )
         => ( ( k8_relat_1 @ ( A @ B ) )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_relat_1])).

thf('1',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_14 @ sk_A_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B @ A ) )
       => ( ( k5_relat_1 @ ( B @ ( k6_relat_1 @ A ) ) )
          = B ) ) ) )).

thf('2',plain,(
    ! [X2304: $i,X2305: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X2304 @ X2305 ) )
      | ( ( k5_relat_1 @ ( X2304 @ ( k6_relat_1 @ X2305 ) ) )
        = X2304 )
      | ~ ( v1_relat_1 @ X2304 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B_14 )
    | ( ( k5_relat_1 @ ( sk_B_14 @ ( k6_relat_1 @ sk_A_5 ) ) )
      = sk_B_14 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k5_relat_1 @ ( sk_B_14 @ ( k6_relat_1 @ sk_A_5 ) ) )
    = sk_B_14 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k8_relat_1 @ ( sk_A_5 @ sk_B_14 ) )
      = sk_B_14 )
    | ~ ( v1_relat_1 @ sk_B_14 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k8_relat_1 @ ( sk_A_5 @ sk_B_14 ) )
    = sk_B_14 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k8_relat_1 @ ( sk_A_5 @ sk_B_14 ) )
 != sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
