%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxtO8FWNy5

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  42 expanded)
%              Number of leaves         :   11 (  17 expanded)
%              Depth                    :   12
%              Number of atoms          :  255 ( 377 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t6_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r1_tarski @ B @ C ) )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X5: $i] :
      ( ( X0
       != ( k1_setfam_1 @ X1 ) )
      | ( r2_hidden @ X5 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X1 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('3',plain,(
    ! [X1: $i,X5: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X5 @ X1 ) @ X1 )
      | ( r2_hidden @ X5 @ ( k1_setfam_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ sk_B @ X11 )
      | ~ ( r2_hidden @ X11 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( sk_D_1 @ X0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_D_1 @ X1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X5: $i] :
      ( ( X0
       != ( k1_setfam_1 @ X1 ) )
      | ( r2_hidden @ X5 @ X0 )
      | ~ ( r2_hidden @ X5 @ ( sk_D_1 @ X5 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('12',plain,(
    ! [X1: $i,X5: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X5 @ ( sk_D_1 @ X5 @ X1 ) )
      | ( r2_hidden @ X5 @ ( k1_setfam_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_B @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( k1_setfam_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).


%------------------------------------------------------------------------------
