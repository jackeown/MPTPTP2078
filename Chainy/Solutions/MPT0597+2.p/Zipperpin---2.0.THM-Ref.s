%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0597+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mmfoxtSxy0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 11.08s
% Output     : Refutation 11.08s
% Verified   : 
% Statistics : Number of formulae       :   21 (  28 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 237 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_34_type,type,(
    sk_C_34: $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) )
        = ( k9_relat_1 @ ( B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X2283: $i,X2284: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( X2283 @ X2284 ) ) )
        = ( k9_relat_1 @ ( X2283 @ X2284 ) ) )
      | ~ ( v1_relat_1 @ X2283 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t201_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( k7_relat_1 @ ( B @ A ) )
              = ( k7_relat_1 @ ( C @ A ) ) )
           => ( ( k9_relat_1 @ ( B @ A ) )
              = ( k9_relat_1 @ ( C @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( ( k7_relat_1 @ ( B @ A ) )
                = ( k7_relat_1 @ ( C @ A ) ) )
             => ( ( k9_relat_1 @ ( B @ A ) )
                = ( k9_relat_1 @ ( C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_relat_1])).

thf('1',plain,
    ( ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
    = ( k7_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X2283: $i,X2284: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( X2283 @ X2284 ) ) )
        = ( k9_relat_1 @ ( X2283 @ X2284 ) ) )
      | ~ ( v1_relat_1 @ X2283 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('3',plain,
    ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) ) )
      = ( k9_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) )
    | ~ ( v1_relat_1 @ sk_C_34 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C_34 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_relat_1 @ ( k7_relat_1 @ ( sk_B_15 @ sk_A_5 ) ) )
    = ( k9_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k9_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
      = ( k9_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) )
    | ~ ( v1_relat_1 @ sk_B_15 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k9_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
    = ( k9_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k9_relat_1 @ ( sk_B_15 @ sk_A_5 ) )
 != ( k9_relat_1 @ ( sk_C_34 @ sk_A_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
