%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0646+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZEmldKpsNm

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 14.35s
% Output     : Refutation 14.35s
% Verified   : 
% Statistics : Number of formulae       :   37 (  57 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 560 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_24_type,type,(
    sk_B_24: $i )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t53_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ ( A @ B ) )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ? [B: $i] :
              ( ( ( k5_relat_1 @ ( A @ B ) )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
              & ( v1_funct_1 @ B )
              & ( v1_relat_1 @ B ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A_7 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k5_relat_1 @ ( sk_A_7 @ sk_B_24 ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A_7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( B @ A ) ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2741: $i,X2742: $i] :
      ( ~ ( v1_relat_1 @ X2741 )
      | ~ ( v1_funct_1 @ X2741 )
      | ( r1_tarski @ ( k2_relat_1 @ X2741 @ ( k1_relat_1 @ X2742 ) ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( X2741 @ X2742 ) ) )
       != ( k1_relat_1 @ X2741 ) )
      | ~ ( v1_funct_1 @ X2742 )
      | ~ ( v1_relat_1 @ X2742 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('3',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_A_7 ) ) )
     != ( k1_relat_1 @ sk_A_7 ) )
    | ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A_7 @ ( k1_relat_1 @ sk_B_24 ) ) )
    | ~ ( v1_funct_1 @ sk_A_7 )
    | ~ ( v1_relat_1 @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('5',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_relat_1 @ sk_A_7 )
     != ( k1_relat_1 @ sk_A_7 ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A_7 @ ( k1_relat_1 @ sk_B_24 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A_7 @ ( k1_relat_1 @ sk_B_24 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ ( B @ A ) ) )
              & ( r1_tarski @ ( k2_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X2764: $i,X2765: $i] :
      ( ~ ( v1_relat_1 @ X2764 )
      | ~ ( v1_funct_1 @ X2764 )
      | ( v2_funct_1 @ X2764 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X2764 @ ( k1_relat_1 @ X2765 ) ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( X2764 @ X2765 ) ) )
      | ~ ( v1_funct_1 @ X2765 )
      | ~ ( v1_relat_1 @ X2765 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B_24 )
    | ~ ( v1_funct_1 @ sk_B_24 )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( sk_A_7 @ sk_B_24 ) ) )
    | ( v2_funct_1 @ sk_A_7 )
    | ~ ( v1_funct_1 @ sk_A_7 )
    | ~ ( v1_relat_1 @ sk_A_7 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_B_24 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k5_relat_1 @ ( sk_A_7 @ sk_B_24 ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ sk_A_7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X2648: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2648 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('17',plain,(
    v1_funct_1 @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A_7 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_funct_1 @ sk_A_7 ),
    inference(demod,[status(thm)],['12','13','14','15','16','17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
