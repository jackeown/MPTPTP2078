%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0149+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BA9ZuY2SwV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    4
%              Number of atoms          :  125 ( 125 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t65_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k2_enumset1 @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) )
        = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k2_enumset1 @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ sk_H ) ) ) ) ) ) ) )
 != ( k2_xboole_0 @ ( k2_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ sk_D_7 ) ) ) @ ( k2_enumset1 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ sk_H ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) @ ( k2_enumset1 @ ( E @ ( F @ ( G @ H ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X469: $i,X470: $i,X471: $i,X472: $i,X473: $i,X474: $i,X475: $i,X476: $i] :
      ( ( k6_enumset1 @ ( X469 @ ( X470 @ ( X471 @ ( X472 @ ( X473 @ ( X474 @ ( X475 @ X476 ) ) ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ ( X469 @ ( X470 @ ( X471 @ X472 ) ) ) @ ( k2_enumset1 @ ( X473 @ ( X474 @ ( X475 @ X476 ) ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('2',plain,(
    ( k6_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ sk_H ) ) ) ) ) ) ) )
 != ( k6_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ ( sk_F @ ( sk_G @ sk_H ) ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
