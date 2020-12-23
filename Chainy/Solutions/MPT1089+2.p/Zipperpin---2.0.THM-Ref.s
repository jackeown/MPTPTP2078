%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1089+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BVjc2kBsNe

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   16 (  22 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :   57 ( 117 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_17_type,type,(
    sk_A_17: $i )).

thf(sk_B_100_type,type,(
    sk_B_100: $i )).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5693: $i,X5694: $i] :
      ( ~ ( v1_funct_1 @ X5693 )
      | ~ ( v1_relat_1 @ X5693 )
      | ~ ( v1_finset_1 @ X5694 )
      | ( v1_finset_1 @ ( k9_relat_1 @ ( X5693 @ X5694 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf(t17_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k9_relat_1 @ ( B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v1_finset_1 @ A )
         => ( v1_finset_1 @ ( k9_relat_1 @ ( B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_finset_1])).

thf('1',plain,(
    ~ ( v1_finset_1 @ ( k9_relat_1 @ ( sk_B_100 @ sk_A_17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( v1_finset_1 @ sk_A_17 )
    | ~ ( v1_relat_1 @ sk_B_100 )
    | ~ ( v1_funct_1 @ sk_B_100 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A_17 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_relat_1 @ sk_B_100 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B_100 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3','4','5'])).

%------------------------------------------------------------------------------
