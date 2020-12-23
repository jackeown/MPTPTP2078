%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0706+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.987VEekJTc

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 16.75s
% Output     : Refutation 16.75s
% Verified   : 
% Statistics : Number of formulae       :   28 (  43 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  155 ( 478 expanded)
%              Number of equality atoms :   14 (  43 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_50_type,type,(
    sk_C_50: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_8_type,type,(
    sk_A_8: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_27_type,type,(
    sk_B_27: $i )).

thf(t161_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k10_relat_1 @ ( C @ A ) )
            = ( k10_relat_1 @ ( C @ B ) ) )
          & ( r1_tarski @ ( A @ ( k2_relat_1 @ C ) ) )
          & ( r1_tarski @ ( B @ ( k2_relat_1 @ C ) ) ) )
       => ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( ( k10_relat_1 @ ( C @ A ) )
              = ( k10_relat_1 @ ( C @ B ) ) )
            & ( r1_tarski @ ( A @ ( k2_relat_1 @ C ) ) )
            & ( r1_tarski @ ( B @ ( k2_relat_1 @ C ) ) ) )
         => ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_funct_1])).

thf('0',plain,(
    r1_tarski @ ( sk_A_8 @ ( k2_relat_1 @ sk_C_50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( A @ ( k2_relat_1 @ B ) ) )
       => ( ( k9_relat_1 @ ( B @ ( k10_relat_1 @ ( B @ A ) ) ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X2783: $i,X2784: $i] :
      ( ~ ( r1_tarski @ ( X2783 @ ( k2_relat_1 @ X2784 ) ) )
      | ( ( k9_relat_1 @ ( X2784 @ ( k10_relat_1 @ ( X2784 @ X2783 ) ) ) )
        = X2783 )
      | ~ ( v1_funct_1 @ X2784 )
      | ~ ( v1_relat_1 @ X2784 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_C_50 )
    | ~ ( v1_funct_1 @ sk_C_50 )
    | ( ( k9_relat_1 @ ( sk_C_50 @ ( k10_relat_1 @ ( sk_C_50 @ sk_A_8 ) ) ) )
      = sk_A_8 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C_50 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_C_50 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ ( sk_C_50 @ ( k10_relat_1 @ ( sk_C_50 @ sk_A_8 ) ) ) )
    = sk_A_8 ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    r1_tarski @ ( sk_B_27 @ ( k2_relat_1 @ sk_C_50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X2783: $i,X2784: $i] :
      ( ~ ( r1_tarski @ ( X2783 @ ( k2_relat_1 @ X2784 ) ) )
      | ( ( k9_relat_1 @ ( X2784 @ ( k10_relat_1 @ ( X2784 @ X2783 ) ) ) )
        = X2783 )
      | ~ ( v1_funct_1 @ X2784 )
      | ~ ( v1_relat_1 @ X2784 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C_50 )
    | ~ ( v1_funct_1 @ sk_C_50 )
    | ( ( k9_relat_1 @ ( sk_C_50 @ ( k10_relat_1 @ ( sk_C_50 @ sk_B_27 ) ) ) )
      = sk_B_27 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_50 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C_50 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k10_relat_1 @ ( sk_C_50 @ sk_A_8 ) )
    = ( k10_relat_1 @ ( sk_C_50 @ sk_B_27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k9_relat_1 @ ( sk_C_50 @ ( k10_relat_1 @ ( sk_C_50 @ sk_A_8 ) ) ) )
    = sk_B_27 ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    sk_A_8 = sk_B_27 ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    sk_A_8 != sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
