%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0154+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AeE4OXXjY9

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :  131 ( 138 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ ( A @ ( A @ B ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ ( A @ ( A @ B ) ) )
        = ( k2_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ sk_B_2 ) ) )
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
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ sk_B_2 ) ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X645: $i] :
      ( ( k2_tarski @ ( X645 @ X645 ) )
      = ( k1_tarski @ X645 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ C ) ) ) ) )).

thf('4',plain,(
    ! [X482: $i,X483: $i,X484: $i] :
      ( ( k1_enumset1 @ ( X482 @ ( X483 @ X484 ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( X482 @ X483 ) @ ( k1_tarski @ X484 ) ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ ( X0 @ ( X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X477: $i,X478: $i] :
      ( ( k2_tarski @ ( X477 @ X478 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X477 @ ( k1_tarski @ X478 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ ( X0 @ ( X0 @ X1 ) ) )
      = ( k2_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('9',plain,(
    ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) )
 != ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['2','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).

%------------------------------------------------------------------------------
