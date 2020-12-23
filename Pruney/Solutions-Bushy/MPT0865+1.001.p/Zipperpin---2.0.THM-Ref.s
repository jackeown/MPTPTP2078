%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0865+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2XcEYi4jr

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  48 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 364 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(t23_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ B )
         => ( A
            = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_tarski @ ( sk_C @ X0 ) @ ( sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( sk_A
      = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t8_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ X5 ) @ ( k2_mcart_1 @ X5 ) )
        = X5 )
      | ( X5
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t8_mcart_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ X6 @ X7 ) ) @ ( k2_mcart_1 @ ( k4_tarski @ X6 @ X7 ) ) )
      = ( k4_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) @ ( k2_mcart_1 @ sk_A ) )
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    sk_A
 != ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).


%------------------------------------------------------------------------------
