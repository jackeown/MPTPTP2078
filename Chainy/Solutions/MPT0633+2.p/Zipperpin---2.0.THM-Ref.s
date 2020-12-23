%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0633+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m254AD7BUG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 19.99s
% Output     : Refutation 19.99s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  109 ( 127 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(sk_B_20_type,type,(
    sk_B_20: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t35_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ ( A @ B ) )
       => ( ( k1_funct_1 @ ( k6_relat_1 @ B @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t35_funct_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_7 @ sk_B_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ ( C @ A ) )
             => ( ( k1_funct_1 @ ( B @ C ) )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X2730: $i,X2731: $i,X2732: $i] :
      ( ( X2731
       != ( k6_relat_1 @ X2730 ) )
      | ( ( k1_funct_1 @ ( X2731 @ X2732 ) )
        = X2732 )
      | ~ ( r2_hidden @ ( X2732 @ X2730 ) )
      | ~ ( v1_funct_1 @ X2731 )
      | ~ ( v1_relat_1 @ X2731 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X2730: $i,X2732: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X2730 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X2730 ) )
      | ~ ( r2_hidden @ ( X2732 @ X2730 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X2730 @ X2732 ) )
        = X2732 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X2637: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X2637 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X2730: $i,X2732: $i] :
      ( ~ ( r2_hidden @ ( X2732 @ X2730 ) )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X2730 @ X2732 ) )
        = X2732 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B_20 @ sk_A_7 ) )
    = sk_A_7 ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ( k1_funct_1 @ ( k6_relat_1 @ sk_B_20 @ sk_A_7 ) )
 != sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
