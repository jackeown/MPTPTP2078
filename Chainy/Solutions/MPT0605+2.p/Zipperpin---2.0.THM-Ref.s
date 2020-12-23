%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0605+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OUELe8Pbzx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 155 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_6_type,type,(
    sk_A_6: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t209_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ ( B @ A ) ) )
     => ( B
        = ( k7_relat_1 @ ( B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v4_relat_1 @ ( B @ A ) ) )
       => ( B
          = ( k7_relat_1 @ ( B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t209_relat_1])).

thf('0',plain,(
    v4_relat_1 @ ( sk_B_15 @ sk_A_6 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X2082: $i,X2083: $i] :
      ( ~ ( v4_relat_1 @ ( X2082 @ X2083 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X2082 @ X2083 ) )
      | ~ ( v1_relat_1 @ X2082 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B_15 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_15 @ sk_A_6 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_15 @ sk_A_6 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B @ A ) )
       => ( ( k7_relat_1 @ ( B @ A ) )
          = B ) ) ) )).

thf('5',plain,(
    ! [X2581: $i,X2582: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2581 @ X2582 ) )
      | ( ( k7_relat_1 @ ( X2581 @ X2582 ) )
        = X2581 )
      | ~ ( v1_relat_1 @ X2581 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_B_15 )
    | ( ( k7_relat_1 @ ( sk_B_15 @ sk_A_6 ) )
      = sk_B_15 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k7_relat_1 @ ( sk_B_15 @ sk_A_6 ) )
    = sk_B_15 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B_15
 != ( k7_relat_1 @ ( sk_B_15 @ sk_A_6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
