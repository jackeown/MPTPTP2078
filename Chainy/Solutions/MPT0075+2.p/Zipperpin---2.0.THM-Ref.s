%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0075+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mlhdViFO2e

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   32 (  42 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 251 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t68_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ ( C @ A ) )
          & ( r1_tarski @ ( C @ B ) )
          & ( r1_xboole_0 @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ~ ( ( r1_tarski @ ( C @ A ) )
            & ( r1_tarski @ ( C @ B ) )
            & ( r1_xboole_0 @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_xboole_1])).

thf('1',plain,(
    r1_tarski @ ( sk_C_5 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_C_5 )
    | ( r2_hidden @ ( sk_B @ sk_C_5 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ ( sk_B @ sk_C_5 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( sk_C_5 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_C_5 )
    | ( r2_hidden @ ( sk_B @ sk_C_5 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( sk_B @ sk_C_5 @ sk_A_2 ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ ( X60 @ X58 ) )
      | ~ ( r2_hidden @ ( X60 @ X61 ) )
      | ~ ( r1_xboole_0 @ ( X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_A_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_C_5 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
