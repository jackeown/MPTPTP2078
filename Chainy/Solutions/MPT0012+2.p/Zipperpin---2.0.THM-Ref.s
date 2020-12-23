%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0012+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O8RvYhXCT7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:41 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  193 ( 243 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t5_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
        = ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
 != ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_A_2 ) @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('6',plain,(
    ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X2 @ X1 ) ) ) )
      = ( k2_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('11',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('12',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X91 @ X92 ) @ X93 ) )
      = ( k2_xboole_0 @ ( X91 @ ( k2_xboole_0 @ ( X92 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( X0 @ X1 ) )
      = ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['6','9','10','13'])).

thf('15',plain,(
    $false ),
    inference(simplify,[status(thm)],['14'])).

%------------------------------------------------------------------------------
