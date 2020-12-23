%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0769+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWPhAVS098

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 10.50s
% Output     : Refutation 10.50s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 164 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_55_type,type,(
    sk_B_55: $i )).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( B @ A ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( A @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X3320: $i,X3321: $i] :
      ( ( ( k2_wellord1 @ ( X3321 @ X3320 ) )
        = ( k7_relat_1 @ ( k8_relat_1 @ ( X3320 @ X3321 ) @ X3320 ) ) )
      | ~ ( v1_relat_1 @ X3321 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t140_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k8_relat_1 @ ( A @ C ) @ B ) )
        = ( k8_relat_1 @ ( A @ ( k7_relat_1 @ ( C @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X2289: $i,X2290: $i,X2291: $i] :
      ( ( ( k7_relat_1 @ ( k8_relat_1 @ ( X2289 @ X2290 ) @ X2291 ) )
        = ( k8_relat_1 @ ( X2289 @ ( k7_relat_1 @ ( X2290 @ X2291 ) ) ) ) )
      | ~ ( v1_relat_1 @ X2290 ) ) ),
    inference(cnf,[status(esa)],[t140_relat_1])).

thf(t18_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( B @ A ) )
        = ( k8_relat_1 @ ( A @ ( k7_relat_1 @ ( B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ ( B @ A ) )
          = ( k8_relat_1 @ ( A @ ( k7_relat_1 @ ( B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_wellord1])).

thf('2',plain,(
    ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) )
 != ( k8_relat_1 @ ( sk_A_14 @ ( k7_relat_1 @ ( sk_B_55 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) )
     != ( k7_relat_1 @ ( k8_relat_1 @ ( sk_A_14 @ sk_B_55 ) @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_55 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_55 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) )
 != ( k7_relat_1 @ ( k8_relat_1 @ ( sk_A_14 @ sk_B_55 ) @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) )
     != ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_55 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_55 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) )
 != ( k2_wellord1 @ ( sk_B_55 @ sk_A_14 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
