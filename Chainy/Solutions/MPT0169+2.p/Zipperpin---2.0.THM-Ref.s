%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0169+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5uoWISk3IJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :  108 ( 108 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t85_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( B @ ( C @ D ) ) ) ) ) ) )
      = ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( A @ ( B @ ( C @ D ) ) ) ) ) ) )
        = ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) ) ) ) )
 != ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )
      = ( k3_enumset1 @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X683: $i,X684: $i,X685: $i,X686: $i,X687: $i] :
      ( ( k5_enumset1 @ ( X683 @ ( X683 @ ( X683 @ ( X684 @ ( X685 @ ( X686 @ X687 ) ) ) ) ) ) )
      = ( k3_enumset1 @ ( X683 @ ( X684 @ ( X685 @ ( X686 @ X687 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ ( A @ ( A @ ( B @ ( C @ D ) ) ) ) )
      = ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X651: $i,X652: $i,X653: $i,X654: $i] :
      ( ( k3_enumset1 @ ( X651 @ ( X651 @ ( X652 @ ( X653 @ X654 ) ) ) ) )
      = ( k2_enumset1 @ ( X651 @ ( X652 @ ( X653 @ X654 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('3',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) )
 != ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
