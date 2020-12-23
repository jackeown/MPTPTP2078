%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0120+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sAY05fOE9q

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 6.92s
% Output     : Refutation 6.92s
% Verified   : 
% Statistics : Number of formulae       :   26 (  42 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :  205 ( 337 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t113_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) @ D ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( B @ C ) @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) @ D ) )
        = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( B @ C ) @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) @ sk_D_4 ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ sk_D_4 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ( k2_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_C_5 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) ) ) )
 != ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1','2','3','4'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X257: $i,X258: $i,X259: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X257 @ X258 ) @ X259 ) )
      = ( k2_xboole_0 @ ( X257 @ ( k2_xboole_0 @ ( X258 @ X259 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X2 @ X1 ) ) ) )
      = ( k2_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X2 @ X1 ) ) ) )
      = ( k2_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X257: $i,X258: $i,X259: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X257 @ X258 ) @ X259 ) )
      = ( k2_xboole_0 @ ( X257 @ ( k2_xboole_0 @ ( X258 @ X259 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( X0 @ ( k2_xboole_0 @ ( X2 @ X1 ) ) ) )
      = ( k2_xboole_0 @ ( X2 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ( k2_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ) )
 != ( k2_xboole_0 @ ( sk_D_4 @ ( k2_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['5','8','9','10','11','12','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
