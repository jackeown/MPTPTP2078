%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AmEnG4ZT5A

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  124 ( 169 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t6_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ B ) )
                & ~ ( r2_hidden @ ( C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_xboole_0])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X75: $i] :
      ( ~ ( r2_hidden @ ( X75 @ sk_B_1 ) )
      | ( r2_hidden @ ( X75 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( X0 @ sk_B_1 ) @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ( r1_tarski @ ( sk_B_1 @ sk_A_2 ) )
    | ( r1_tarski @ ( sk_B_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( sk_B_1 @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,
    ( ( sk_B_1 = sk_A_2 )
    | ( r2_xboole_0 @ ( sk_B_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
     => ~ ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_xboole_0 @ ( X2 @ X3 ) )
      | ~ ( r2_xboole_0 @ ( X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('11',plain,(
    ~ ( r2_xboole_0 @ ( sk_B_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_B_1 = sk_A_2 ),
    inference(clc,[status(thm)],['8','11'])).

thf('13',plain,(
    r2_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['0','12'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ ( A @ A ) ) )).

thf('14',plain,(
    ! [X45: $i] :
      ~ ( r2_xboole_0 @ ( X45 @ X45 ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('15',plain,(
    $false ),
    inference('sup-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
