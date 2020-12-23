%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0013+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OD8lxxy09Q

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :    7 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  129 ( 150 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t6_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
        = ( k2_xboole_0 @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) )
 != ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ X1 ) )
      = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ X1 ) )
      = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
 != ( k2_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
