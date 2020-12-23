%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0074+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p5HAv6t4Mc

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   14 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 313 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t67_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( A @ C ) )
          & ( r1_xboole_0 @ ( B @ C ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t67_xboole_1])).

thf('3',plain,(
    r1_tarski @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_C_5 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_A_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A_2 @ sk_C_5 ) ),
    inference('simplify_reflect-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A_2 @ sk_B_2 ) ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X58: $i,X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ ( X60 @ X58 ) )
      | ~ ( r2_hidden @ ( X60 @ X61 ) )
      | ~ ( r1_xboole_0 @ ( X58 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_B_2 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21'])).

%------------------------------------------------------------------------------
