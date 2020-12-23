%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0019+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N33oFuSr63

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :  143 ( 175 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t12_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( ( k2_xboole_0 @ ( A @ B ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ B ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf('3',plain,(
    ! [X112: $i,X113: $i,X114: $i] :
      ( ~ ( r1_tarski @ ( X112 @ X113 ) )
      | ~ ( r1_tarski @ ( X114 @ X113 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ ( X112 @ X114 ) @ X113 ) ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_B_2 ) )
      | ~ ( r1_tarski @ ( X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( sk_B_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
    | ( sk_B_2
      = ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X108: $i,X109: $i] :
      ( r1_tarski @ ( X108 @ ( k2_xboole_0 @ ( X108 @ X109 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('11',plain,
    ( sk_B_2
    = ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
 != sk_B_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

%------------------------------------------------------------------------------
