%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0164+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.e4JDnXjKmz

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   17 (  17 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :  119 ( 119 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t80_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )
      = ( k3_enumset1 @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k5_enumset1 @ ( A @ ( A @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )
        = ( k3_enumset1 @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ sk_E_1 ) ) ) ) ) ) )
 != ( k3_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ sk_E_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ ( A @ ( A @ ( B @ ( C @ ( D @ ( E @ F ) ) ) ) ) ) )
      = ( k4_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ F ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X660: $i,X661: $i,X662: $i,X663: $i,X664: $i,X665: $i] :
      ( ( k5_enumset1 @ ( X660 @ ( X660 @ ( X661 @ ( X662 @ ( X663 @ ( X664 @ X665 ) ) ) ) ) ) )
      = ( k4_enumset1 @ ( X660 @ ( X661 @ ( X662 @ ( X663 @ ( X664 @ X665 ) ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ ( A @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) )
      = ( k3_enumset1 @ ( A @ ( B @ ( C @ ( D @ E ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X655: $i,X656: $i,X657: $i,X658: $i,X659: $i] :
      ( ( k4_enumset1 @ ( X655 @ ( X655 @ ( X656 @ ( X657 @ ( X658 @ X659 ) ) ) ) ) )
      = ( k3_enumset1 @ ( X655 @ ( X656 @ ( X657 @ ( X658 @ X659 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('3',plain,(
    ( k3_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ sk_E_1 ) ) ) ) )
 != ( k3_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ sk_E_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    $false ),
    inference(simplify,[status(thm)],['3'])).

%------------------------------------------------------------------------------
