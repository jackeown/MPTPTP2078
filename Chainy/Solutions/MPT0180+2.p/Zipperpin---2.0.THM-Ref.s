%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0180+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.02ASZjIGUk

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:48 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   80 (  80 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t96_enumset1,conjecture,(
    ! [A: $i] :
      ( ( k6_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ A ) ) ) ) ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k6_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ A ) ) ) ) ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t96_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ sk_A_2 ) ) ) ) ) ) ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ ( A @ B ) ) ) ) ) ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('1',plain,(
    ! [X726: $i,X727: $i] :
      ( ( k6_enumset1 @ ( X726 @ ( X726 @ ( X726 @ ( X726 @ ( X726 @ ( X726 @ ( X726 @ X727 ) ) ) ) ) ) ) )
      = ( k2_tarski @ ( X726 @ X727 ) ) ) ),
    inference(cnf,[status(esa)],[t95_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ ( A @ A ) )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X645: $i] :
      ( ( k2_tarski @ ( X645 @ X645 ) )
      = ( k1_tarski @ X645 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ( k1_tarski @ sk_A_2 )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
