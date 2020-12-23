%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0137+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cKjM3eEYge

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    4
%              Number of atoms          :  101 ( 101 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(sk_D_7_type,type,(
    sk_D_7: $i )).

thf(t53_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ F ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ ( A @ ( B @ C ) ) @ ( k1_enumset1 @ ( D @ ( E @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( k4_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ F ) ) ) ) ) )
        = ( k2_xboole_0 @ ( k1_enumset1 @ ( A @ ( B @ C ) ) @ ( k1_enumset1 @ ( D @ ( E @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ sk_F ) ) ) ) ) )
 != ( k2_xboole_0 @ ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) @ ( k1_enumset1 @ ( sk_D_7 @ ( sk_E_1 @ sk_F ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ ( A @ ( B @ ( C @ ( D @ ( E @ F ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ ( A @ ( B @ C ) ) @ ( k1_enumset1 @ ( D @ ( E @ F ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X456: $i,X457: $i,X458: $i,X459: $i,X460: $i,X461: $i] :
      ( ( k4_enumset1 @ ( X456 @ ( X457 @ ( X458 @ ( X459 @ ( X460 @ X461 ) ) ) ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ ( X456 @ ( X457 @ X458 ) ) @ ( k1_enumset1 @ ( X459 @ ( X460 @ X461 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('2',plain,(
    ( k4_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ sk_F ) ) ) ) ) )
 != ( k4_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_D_7 @ ( sk_E_1 @ sk_F ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
