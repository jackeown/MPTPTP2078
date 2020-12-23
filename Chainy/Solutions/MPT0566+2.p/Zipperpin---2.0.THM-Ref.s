%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0566+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h7z0UOgsPy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   83 ( 123 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(sk_B_14_type,type,(
    sk_B_14: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ ( B @ A ) @ ( k1_relat_1 @ B ) ) ) ) )).

thf('0',plain,(
    ! [X2321: $i,X2322: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( X2321 @ X2322 ) @ ( k1_relat_1 @ X2321 ) ) )
      | ~ ( v1_relat_1 @ X2321 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ ( A @ ( k2_relat_1 @ A ) ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2325: $i] :
      ( ( ( k10_relat_1 @ ( X2325 @ ( k2_relat_1 @ X2325 ) ) )
        = ( k1_relat_1 @ X2325 ) )
      | ~ ( v1_relat_1 @ X2325 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ ( B @ A ) @ ( k10_relat_1 @ ( B @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ ( B @ A ) @ ( k10_relat_1 @ ( B @ ( k2_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t170_relat_1])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k10_relat_1 @ ( sk_B_14 @ ( k2_relat_1 @ sk_B_14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k1_relat_1 @ sk_B_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_14 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k1_relat_1 @ sk_B_14 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_relat_1 @ sk_B_14 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
