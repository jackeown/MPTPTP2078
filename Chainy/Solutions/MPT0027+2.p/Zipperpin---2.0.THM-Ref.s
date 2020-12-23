%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0027+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.svHLlGvqEq

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   10
%              Number of atoms          :  215 ( 385 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X107: $i,X108: $i,X109: $i] :
      ( ( r1_tarski @ ( X107 @ X108 ) )
      | ~ ( r1_tarski @ ( X107 @ ( k3_xboole_0 @ ( X108 @ X109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t20_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) )
        & ! [D: $i] :
            ( ( ( r1_tarski @ ( D @ B ) )
              & ( r1_tarski @ ( D @ C ) ) )
           => ( r1_tarski @ ( D @ A ) ) ) )
     => ( A
        = ( k3_xboole_0 @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ B ) )
          & ( r1_tarski @ ( A @ C ) )
          & ! [D: $i] :
              ( ( ( r1_tarski @ ( D @ B ) )
                & ( r1_tarski @ ( D @ C ) ) )
             => ( r1_tarski @ ( D @ A ) ) ) )
       => ( A
          = ( k3_xboole_0 @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_xboole_1])).

thf('6',plain,(
    ! [X117: $i] :
      ( ( r1_tarski @ ( X117 @ sk_A_2 ) )
      | ~ ( r1_tarski @ ( X117 @ sk_C_5 ) )
      | ~ ( r1_tarski @ ( X117 @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_B_2 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ ( X0 @ sk_C_5 ) @ sk_B_2 ) )
      | ( r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ X0 ) @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ sk_A_2 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    | ( sk_A_2
      = ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A_2
 != ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) ) )
     => ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X110: $i,X111: $i,X112: $i] :
      ( ~ ( r1_tarski @ ( X110 @ X111 ) )
      | ~ ( r1_tarski @ ( X110 @ X112 ) )
      | ( r1_tarski @ ( X110 @ ( k3_xboole_0 @ ( X111 @ X112 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) )
      | ~ ( r1_tarski @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['15','20'])).

%------------------------------------------------------------------------------
