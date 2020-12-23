%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0188+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2iOK4tLoqU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:48 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   16 (  17 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :  111 ( 122 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t107_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( A @ ( D @ ( C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k2_enumset1 @ ( A @ ( D @ ( C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) )
 != ( k2_enumset1 @ ( sk_A_2 @ ( sk_D_7 @ ( sk_C_6 @ sk_B_2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( A @ ( B @ ( D @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X483: $i,X484: $i,X485: $i,X486: $i] :
      ( ( k2_enumset1 @ ( X483 @ ( X484 @ ( X486 @ X485 ) ) ) )
      = ( k2_enumset1 @ ( X483 @ ( X484 @ ( X485 @ X486 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) )
 != ( k2_enumset1 @ ( sk_A_2 @ ( sk_D_7 @ ( sk_B_2 @ sk_C_6 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( A @ ( C @ ( B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X487: $i,X488: $i,X489: $i,X490: $i] :
      ( ( k2_enumset1 @ ( X487 @ ( X489 @ ( X488 @ X490 ) ) ) )
      = ( k2_enumset1 @ ( X487 @ ( X488 @ ( X489 @ X490 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('4',plain,(
    ! [X483: $i,X484: $i,X485: $i,X486: $i] :
      ( ( k2_enumset1 @ ( X483 @ ( X484 @ ( X486 @ X485 ) ) ) )
      = ( k2_enumset1 @ ( X483 @ ( X484 @ ( X485 @ X486 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t103_enumset1])).

thf('5',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) )
 != ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).

%------------------------------------------------------------------------------
