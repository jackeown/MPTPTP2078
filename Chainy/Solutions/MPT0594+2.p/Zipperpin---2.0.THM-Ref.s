%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0594+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MItaocX5j0

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 12.55s
% Output     : Refutation 12.55s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 ( 359 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_33_type,type,(
    sk_C_33: $i )).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
            = ( k10_relat_1 @ ( A @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2364: $i,X2365: $i] :
      ( ~ ( v1_relat_1 @ X2364 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( X2365 @ X2364 ) ) )
        = ( k10_relat_1 @ ( X2365 @ ( k1_relat_1 @ X2364 ) ) ) )
      | ~ ( v1_relat_1 @ X2365 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('1',plain,(
    ! [X2364: $i,X2365: $i] :
      ( ~ ( v1_relat_1 @ X2364 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( X2365 @ X2364 ) ) )
        = ( k10_relat_1 @ ( X2365 @ ( k1_relat_1 @ X2364 ) ) ) )
      | ~ ( v1_relat_1 @ X2365 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t198_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ ( C @ A ) ) )
                  = ( k1_relat_1 @ ( k5_relat_1 @ ( C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( ( k1_relat_1 @ A )
                    = ( k1_relat_1 @ B ) )
                 => ( ( k1_relat_1 @ ( k5_relat_1 @ ( C @ A ) ) )
                    = ( k1_relat_1 @ ( k5_relat_1 @ ( C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t198_relat_1])).

thf('2',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C_33 @ sk_A_5 ) ) )
 != ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C_33 @ sk_B_15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C_33 @ sk_A_5 ) ) )
     != ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_B_15 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_33 )
    | ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_relat_1 @ sk_A_5 )
    = ( k1_relat_1 @ sk_B_15 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_C_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ ( sk_C_33 @ sk_A_5 ) ) )
 != ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_A_5 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_A_5 ) ) )
     != ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_A_5 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_33 )
    | ~ ( v1_relat_1 @ sk_A_5 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_A_5 ) ) )
 != ( k10_relat_1 @ ( sk_C_33 @ ( k1_relat_1 @ sk_A_5 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
