%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0709+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U7YoiVMP91

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 17.61s
% Output     : Refutation 17.61s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  167 ( 337 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_27_type,type,(
    sk_B_27: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_9_type,type,(
    sk_A_9: $i )).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ ( B @ ( k9_relat_1 @ ( B @ A ) ) ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2798: $i,X2799: $i] :
      ( ~ ( v2_funct_1 @ X2798 )
      | ( r1_tarski @ ( k10_relat_1 @ ( X2798 @ ( k9_relat_1 @ ( X2798 @ X2799 ) ) ) @ X2799 ) )
      | ~ ( v1_funct_1 @ X2798 )
      | ~ ( v1_relat_1 @ X2798 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ ( B @ ( k9_relat_1 @ ( B @ A ) ) ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ ( B @ ( k9_relat_1 @ ( B @ A ) ) ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('1',plain,(
    r1_tarski @ ( sk_A_9 @ ( k1_relat_1 @ sk_B_27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
       => ( r1_tarski @ ( A @ ( k10_relat_1 @ ( B @ ( k9_relat_1 @ ( B @ A ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2781: $i,X2782: $i] :
      ( ~ ( r1_tarski @ ( X2781 @ ( k1_relat_1 @ X2782 ) ) )
      | ( r1_tarski @ ( X2781 @ ( k10_relat_1 @ ( X2782 @ ( k9_relat_1 @ ( X2782 @ X2781 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X2782 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B_27 )
    | ( r1_tarski @ ( sk_A_9 @ ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( sk_A_9 @ ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) @ sk_A_9 ) )
    | ( ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) )
      = sk_A_9 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) )
 != sk_A_9 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ ( sk_B_27 @ ( k9_relat_1 @ ( sk_B_27 @ sk_A_9 ) ) ) @ sk_A_9 ) ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B_27 )
    | ~ ( v1_funct_1 @ sk_B_27 )
    | ~ ( v2_funct_1 @ sk_B_27 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_funct_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11','12','13'])).

%------------------------------------------------------------------------------
