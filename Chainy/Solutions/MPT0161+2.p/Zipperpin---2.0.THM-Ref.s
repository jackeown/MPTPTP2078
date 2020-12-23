%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0161+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1eokXS2p2Y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  101 ( 108 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t77_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ ( A @ ( A @ ( A @ B ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_enumset1 @ ( A @ ( A @ ( A @ B ) ) ) )
        = ( k2_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('2',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ ( A @ ( A @ ( B @ C ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X648: $i,X649: $i,X650: $i] :
      ( ( k2_enumset1 @ ( X648 @ ( X648 @ ( X649 @ X650 ) ) ) )
      = ( k1_enumset1 @ ( X648 @ ( X649 @ X650 ) ) ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ ( A @ ( A @ B ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X646: $i,X647: $i] :
      ( ( k1_enumset1 @ ( X646 @ ( X646 @ X647 ) ) )
      = ( k2_tarski @ ( X646 @ X647 ) ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).

%------------------------------------------------------------------------------
