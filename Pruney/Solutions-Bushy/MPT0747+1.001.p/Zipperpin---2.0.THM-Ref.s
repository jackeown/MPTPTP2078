%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0747+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S0ILV0ap41

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:26 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 116 expanded)
%              Number of leaves         :   18 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  367 ( 718 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(cc2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) )
     => ( v3_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v3_ordinal1 @ X2 )
      | ~ ( v2_ordinal1 @ X2 )
      | ~ ( v1_ordinal1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_ordinal1])).

thf(t37_ordinal1,conjecture,(
    ! [A: $i] :
      ~ ! [B: $i] :
          ( ( r2_hidden @ B @ A )
        <=> ( v3_ordinal1 @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ! [B: $i] :
            ( ( r2_hidden @ B @ A )
          <=> ( v3_ordinal1 @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t37_ordinal1])).

thf('1',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ X19 @ sk_A )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ X19 @ sk_A )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ~ ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v3_ordinal1 @ X14 )
      | ~ ( v3_ordinal1 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ X19 @ sk_A )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X13 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X13 @ X11 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ~ ( r1_tarski @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('17',plain,
    ( ~ ( v3_ordinal1 @ ( sk_B @ sk_A ) )
    | ( v1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( v1_ordinal1 @ X5 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('19',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_ordinal1 @ sk_A ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','21'])).

thf(d3_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v2_ordinal1 @ A )
    <=> ! [B: $i,C: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ B @ C )
            & ( B != C )
            & ~ ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('24',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( v3_ordinal1 @ X18 )
      | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v3_ordinal1 @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v3_ordinal1 @ X16 )
      | ( r2_hidden @ X17 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( v3_ordinal1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ~ ( r2_hidden @ ( sk_C @ X9 ) @ ( sk_B_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( sk_C @ X0 ) )
      | ( ( sk_C @ X0 )
        = ( sk_B_1 @ X0 ) )
      | ~ ( v3_ordinal1 @ ( sk_B_1 @ X0 ) )
      | ( v2_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( v2_ordinal1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_A ) @ ( sk_C @ sk_A ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ~ ( r2_hidden @ ( sk_B_1 @ X9 ) @ ( sk_C @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('37',plain,
    ( ( v2_ordinal1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','21'])).

thf('39',plain,
    ( ( sk_C @ sk_A )
    = ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( v2_ordinal1 @ X9 )
      | ( ( sk_B_1 @ X9 )
       != ( sk_C @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d3_ordinal1])).

thf('41',plain,
    ( ( ( sk_B_1 @ sk_A )
     != ( sk_B_1 @ sk_A ) )
    | ( v2_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_ordinal1 @ sk_A ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['22','42'])).


%------------------------------------------------------------------------------
