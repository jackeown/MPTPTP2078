%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0173+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rOyt9m2K6u

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:48 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   97 (  97 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t89_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( A @ ( B @ C ) ) ) ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( A @ ( B @ C ) ) ) ) ) ) )
        = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t89_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ) ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( B @ ( C @ D ) ) ) ) ) ) )
      = ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X700: $i,X701: $i,X702: $i,X703: $i] :
      ( ( k5_enumset1 @ ( X700 @ ( X700 @ ( X700 @ ( X700 @ ( X701 @ ( X702 @ X703 ) ) ) ) ) ) )
      = ( k2_enumset1 @ ( X700 @ ( X701 @ ( X702 @ X703 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t85_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ ( A @ ( A @ ( B @ C ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X648: $i,X649: $i,X650: $i] :
      ( ( k2_enumset1 @ ( X648 @ ( X648 @ ( X649 @ X650 ) ) ) )
      = ( k1_enumset1 @ ( X648 @ ( X649 @ X650 ) ) ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
