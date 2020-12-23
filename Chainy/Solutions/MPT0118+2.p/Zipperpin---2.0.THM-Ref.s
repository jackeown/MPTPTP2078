%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0118+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Lgu4NyIeTP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   22 (  25 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  177 ( 202 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t111_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( C @ B ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( C @ B ) ) ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ ( A @ C ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t111_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('5',plain,(
    ! [X247: $i,X248: $i,X249: $i] :
      ( ( k3_xboole_0 @ ( X247 @ ( k4_xboole_0 @ ( X248 @ X249 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X247 @ X248 ) @ X249 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,(
    ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X254: $i,X255: $i,X256: $i] :
      ( ( k3_xboole_0 @ ( X254 @ ( k4_xboole_0 @ ( X255 @ X256 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X254 @ X255 ) @ ( k3_xboole_0 @ ( X254 @ X256 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('8',plain,(
    ! [X247: $i,X248: $i,X249: $i] :
      ( ( k3_xboole_0 @ ( X247 @ ( k4_xboole_0 @ ( X248 @ X249 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X247 @ X248 ) @ X249 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('9',plain,(
    ! [X254: $i,X255: $i,X256: $i] :
      ( ( k3_xboole_0 @ ( X254 @ ( k4_xboole_0 @ ( X255 @ X256 ) ) ) )
      = ( k3_xboole_0 @ ( X254 @ ( k4_xboole_0 @ ( X255 @ ( k3_xboole_0 @ ( X254 @ X256 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
