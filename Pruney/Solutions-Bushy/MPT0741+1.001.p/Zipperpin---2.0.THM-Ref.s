%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2Rk078saZn

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  256 ( 392 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_ordinal1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( ( v3_ordinal1 @ B )
            & ( r1_tarski @ B @ A ) ) )
     => ( v3_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( ( v3_ordinal1 @ B )
              & ( r1_tarski @ B @ A ) ) )
       => ( v3_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t31_ordinal1])).

thf('0',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v2_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_B_1 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( v3_ordinal1 @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( v2_ordinal1 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( v3_ordinal1 @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v3_ordinal1 @ X9 )
      | ( r2_hidden @ X10 @ X9 )
      | ( X10 = X9 )
      | ( r2_hidden @ X9 @ X10 )
      | ~ ( v3_ordinal1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('8',plain,(
    ! [X6: $i] :
      ( ( v2_ordinal1 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 ) @ ( sk_B_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( sk_C @ X0 ) )
      | ( ( sk_C @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( v2_ordinal1 @ X6 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X6 ) @ ( sk_C @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('15',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( v2_ordinal1 @ X6 )
      | ( ( sk_B_1 @ X6 )
       != ( sk_C @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('17',plain,(
    v2_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(d4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
    <=> ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( v3_ordinal1 @ X8 )
      | ~ ( v2_ordinal1 @ X8 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_ordinal1])).

thf('19',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_ordinal1 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ sk_A )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( r1_tarski @ ( sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( v1_ordinal1 @ X2 )
      | ~ ( r1_tarski @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('24',plain,(
    v1_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    v3_ordinal1 @ sk_A ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).


%------------------------------------------------------------------------------
