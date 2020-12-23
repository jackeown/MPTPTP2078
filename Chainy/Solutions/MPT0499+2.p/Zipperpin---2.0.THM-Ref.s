%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0499+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xwnsWu1v6h

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 11.41s
% Output     : Refutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :   23 (  29 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 172 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(t97_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B @ A ) )
       => ( ( k7_relat_1 @ ( B @ A ) )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k1_relat_1 @ B @ A ) )
         => ( ( k7_relat_1 @ ( B @ A ) )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_relat_1])).

thf('0',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_15 @ sk_A_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B @ A ) )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A @ B ) )
          = B ) ) ) )).

thf('1',plain,(
    ! [X2231: $i,X2232: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2231 @ X2232 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X2232 @ X2231 ) )
        = X2231 )
      | ~ ( v1_relat_1 @ X2231 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B_15 )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A_5 @ sk_B_15 ) )
      = sk_B_15 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A_5 @ sk_B_15 ) )
    = sk_B_15 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ ( B @ A ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X2260: $i,X2261: $i] :
      ( ( ( k7_relat_1 @ ( X2261 @ X2260 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X2260 @ X2261 ) ) )
      | ~ ( v1_relat_1 @ X2261 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,
    ( ( ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
      = sk_B_15 )
    | ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
    = sk_B_15 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
 != sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
