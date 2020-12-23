%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0204+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.anXbEohT5O

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :  137 ( 137 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_I_type,type,(
    sk_I: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t130_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k3_enumset1 @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) )
        = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k3_enumset1 @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ ( sk_H @ sk_I ) ) ) ) ) ) ) ) )
 != ( k2_xboole_0 @ ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) @ ( k3_enumset1 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ ( sk_H @ sk_I ) ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l142_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k3_enumset1 @ ( E @ ( F @ ( G @ ( H @ I ) ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X455: $i,X456: $i,X457: $i,X458: $i,X459: $i,X460: $i,X461: $i,X462: $i,X463: $i] :
      ( ( k7_enumset1 @ ( X455 @ ( X456 @ ( X457 @ ( X458 @ ( X459 @ ( X460 @ ( X461 @ ( X462 @ X463 ) ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( X455 @ ( X456 @ ( X457 @ X458 ) ) ) @ ( k3_enumset1 @ ( X459 @ ( X460 @ ( X461 @ ( X462 @ X463 ) ) ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l142_enumset1])).

thf('2',plain,(
    ( k7_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ ( sk_H @ sk_I ) ) ) ) ) ) ) ) )
 != ( k7_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ ( sk_H @ sk_I ) ) ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
