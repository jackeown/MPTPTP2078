%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0005+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YvuLwwDq0I

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  71 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 756 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t5_xboole_0,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( A @ B ) )
        & ( r2_hidden @ ( C @ ( k2_xboole_0 @ ( A @ B ) ) ) )
        & ~ ( ( r2_hidden @ ( C @ A ) )
            & ~ ( r2_hidden @ ( C @ B ) ) )
        & ~ ( ( r2_hidden @ ( C @ B ) )
            & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( A @ B ) )
          & ( r2_hidden @ ( C @ ( k2_xboole_0 @ ( A @ B ) ) ) )
          & ~ ( ( r2_hidden @ ( C @ A ) )
              & ~ ( r2_hidden @ ( C @ B ) ) )
          & ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_xboole_0])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
   <= ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) )
   <= ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X48: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ ( X50 @ X48 ) )
      | ~ ( r2_hidden @ ( X50 @ X51 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
        | ~ ( r2_hidden @ ( sk_C_3 @ X0 ) ) )
   <= ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
   <= ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','10','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_C_3 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X15 @ X13 ) )
      | ( r2_hidden @ ( X15 @ X14 ) )
      | ( r2_hidden @ ( X15 @ X12 ) )
      | ( X13
       != ( k2_xboole_0 @ ( X14 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( X15 @ X12 ) )
      | ( r2_hidden @ ( X15 @ X14 ) )
      | ~ ( r2_hidden @ ( X15 @ ( k2_xboole_0 @ ( X14 @ X12 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_C_3 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) )
   <= ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['3','10'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( sk_C_3 @ sk_A_2 ) ) ),
    inference(simpl_trail,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_C_3 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['13','21'])).

%------------------------------------------------------------------------------
