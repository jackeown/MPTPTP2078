%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0005+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3TD4K3tNYN

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  71 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 756 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t5_xboole_0,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( ( r2_hidden @ C @ A )
            & ~ ( r2_hidden @ C @ B ) )
        & ~ ( ( r2_hidden @ C @ B )
            & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ A @ B )
          & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
          & ~ ( ( r2_hidden @ C @ A )
              & ~ ( r2_hidden @ C @ B ) )
          & ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_xboole_0])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_C_1 @ X0 ) )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','10','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    r2_hidden @ sk_C_1 @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','10'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(clc,[status(thm)],['17','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['13','21'])).


%------------------------------------------------------------------------------
