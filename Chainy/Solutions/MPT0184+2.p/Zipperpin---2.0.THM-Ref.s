%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0184+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.luit1ux8H5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:48 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   14 (  14 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   82 (  82 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t102_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( C @ ( B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
        = ( k1_enumset1 @ ( C @ ( B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t102_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) )
 != ( k1_enumset1 @ ( sk_C_6 @ ( sk_B_2 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( B @ ( C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X477: $i,X478: $i,X479: $i] :
      ( ( k1_enumset1 @ ( X479 @ ( X477 @ X478 ) ) )
      = ( k1_enumset1 @ ( X477 @ ( X478 @ X479 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_C_6 @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( A @ ( C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X732: $i,X733: $i,X734: $i] :
      ( ( k1_enumset1 @ ( X732 @ ( X734 @ X733 ) ) )
      = ( k1_enumset1 @ ( X732 @ ( X733 @ X734 ) ) ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('4',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    $false ),
    inference(simplify,[status(thm)],['4'])).

%------------------------------------------------------------------------------
