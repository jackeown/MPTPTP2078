%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0727+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SNgm9xdiES

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   17 (  28 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 ( 130 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_12_type,type,(
    sk_A_12: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_30_type,type,(
    sk_B_30: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t7_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_hidden @ ( A @ B ) )
          & ( r1_tarski @ ( B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_ordinal1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_12 @ sk_B_30 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_B_30 @ sk_A_12 ) ),
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
      ( ( r2_hidden @ ( X0 @ sk_A_12 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_B_30 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( sk_A_12 @ sk_A_12 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( X0 @ X1 ) )
      | ~ ( r2_hidden @ ( X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('6',plain,(
    ~ ( r2_hidden @ ( sk_A_12 @ sk_A_12 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_A_12 @ sk_A_12 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
