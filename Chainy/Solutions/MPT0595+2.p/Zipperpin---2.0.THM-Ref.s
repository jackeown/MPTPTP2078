%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0595+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YnKIRD9yBJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 16.27s
% Output     : Refutation 16.27s
% Verified   : 
% Statistics : Number of formulae       :   23 (  34 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  146 ( 359 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_33_type,type,(
    sk_C_33: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ ( A @ B ) ) )
            = ( k9_relat_1 @ ( B @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X2315: $i,X2316: $i] :
      ( ~ ( v1_relat_1 @ X2315 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( X2316 @ X2315 ) ) )
        = ( k9_relat_1 @ ( X2315 @ ( k2_relat_1 @ X2316 ) ) ) )
      | ~ ( v1_relat_1 @ X2316 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('1',plain,(
    ! [X2315: $i,X2316: $i] :
      ( ~ ( v1_relat_1 @ X2315 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( X2316 @ X2315 ) ) )
        = ( k9_relat_1 @ ( X2315 @ ( k2_relat_1 @ X2316 ) ) ) )
      | ~ ( v1_relat_1 @ X2316 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t199_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k2_relat_1 @ A )
                  = ( k2_relat_1 @ B ) )
               => ( ( k2_relat_1 @ ( k5_relat_1 @ ( A @ C ) ) )
                  = ( k2_relat_1 @ ( k5_relat_1 @ ( B @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( ( ( k2_relat_1 @ A )
                    = ( k2_relat_1 @ B ) )
                 => ( ( k2_relat_1 @ ( k5_relat_1 @ ( A @ C ) ) )
                    = ( k2_relat_1 @ ( k5_relat_1 @ ( B @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t199_relat_1])).

thf('2',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( sk_A_5 @ sk_C_33 ) ) )
 != ( k2_relat_1 @ ( k5_relat_1 @ ( sk_B_15 @ sk_C_33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( sk_A_5 @ sk_C_33 ) ) )
     != ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_B_15 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_15 )
    | ~ ( v1_relat_1 @ sk_C_33 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_A_5 )
    = ( k2_relat_1 @ sk_B_15 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_C_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ ( sk_A_5 @ sk_C_33 ) ) )
 != ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_A_5 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( ( ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_A_5 ) ) )
     != ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_A_5 ) ) ) )
    | ~ ( v1_relat_1 @ sk_A_5 )
    | ~ ( v1_relat_1 @ sk_C_33 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C_33 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_A_5 ) ) )
 != ( k9_relat_1 @ ( sk_C_33 @ ( k2_relat_1 @ sk_A_5 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
