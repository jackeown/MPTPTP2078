%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0211+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7JtGq0tVsD

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:49 EST 2020

% Result     : Theorem 11.45s
% Output     : Refutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :   13 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  213 ( 240 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t137_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ ( B @ A ) @ ( k2_tarski @ ( C @ A ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ ( B @ A ) @ ( k2_tarski @ ( C @ A ) ) ) )
        = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t137_enumset1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) @ ( k2_tarski @ ( sk_C_6 @ sk_A_2 ) ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( B @ ( C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('2',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('3',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) @ ( k2_tarski @ ( sk_C_6 @ sk_A_2 ) ) ) )
 != ( k1_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k2_tarski @ ( C @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X514: $i,X515: $i,X516: $i,X517: $i] :
      ( ( k2_enumset1 @ ( X514 @ ( X515 @ ( X516 @ X517 ) ) ) )
      = ( k2_xboole_0 @ ( k2_tarski @ ( X514 @ X515 ) @ ( k2_tarski @ ( X516 @ X517 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf(t104_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( A @ ( C @ ( B @ D ) ) ) ) ) )).

thf('5',plain,(
    ! [X554: $i,X555: $i,X556: $i,X557: $i] :
      ( ( k2_enumset1 @ ( X554 @ ( X556 @ ( X555 @ X557 ) ) ) )
      = ( k2_enumset1 @ ( X554 @ ( X555 @ ( X556 @ X557 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t104_enumset1])).

thf('6',plain,(
    ( k2_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ ( sk_A_2 @ sk_A_2 ) ) ) )
 != ( k1_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t118_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_enumset1 @ ( C @ ( D @ ( A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X598: $i,X599: $i,X600: $i,X601: $i] :
      ( ( k2_enumset1 @ ( X600 @ ( X601 @ ( X598 @ X599 ) ) ) )
      = ( k2_enumset1 @ ( X598 @ ( X599 @ ( X600 @ X601 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t118_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ ( A @ ( A @ ( B @ C ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X870: $i,X871: $i,X872: $i] :
      ( ( k2_enumset1 @ ( X870 @ ( X870 @ ( X871 @ X872 ) ) ) )
      = ( k1_enumset1 @ ( X870 @ ( X871 @ X872 ) ) ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ ( X2 @ ( X1 @ ( X0 @ X0 ) ) ) )
      = ( k1_enumset1 @ ( X0 @ ( X2 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('11',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf('12',plain,(
    ( k1_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ sk_A_2 ) ) )
 != ( k1_enumset1 @ ( sk_B_2 @ ( sk_C_6 @ sk_A_2 ) ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
