%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0006+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o4Y27OwUwr

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 181 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t6_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ~ ( r2_hidden @ C @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_xboole_0])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ X9 @ sk_B )
      | ( r2_hidden @ X9 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['5'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,
    ( ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('11',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B = sk_A ),
    inference(clc,[status(thm)],['8','11'])).

thf('13',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 != X7 )
      | ~ ( r2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,(
    ! [X7: $i] :
      ~ ( r2_xboole_0 @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference('sup-',[status(thm)],['13','15'])).


%------------------------------------------------------------------------------
