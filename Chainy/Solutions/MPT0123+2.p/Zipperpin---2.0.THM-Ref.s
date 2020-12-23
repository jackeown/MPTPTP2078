%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0123+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sp9jMd2g0d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  180 ( 205 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t116_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        = ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X166: $i,X167: $i,X168: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X166 @ X167 ) @ X168 ) )
      = ( k3_xboole_0 @ ( X166 @ ( k3_xboole_0 @ ( X167 @ X168 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X166: $i,X167: $i,X168: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X166 @ X167 ) @ X168 ) )
      = ( k3_xboole_0 @ ( X166 @ ( k3_xboole_0 @ ( X167 @ X168 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X2 @ X1 ) ) ) )
      = ( k3_xboole_0 @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('7',plain,(
    ! [X169: $i,X170: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X169 @ X170 ) @ X169 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X204: $i,X205: $i] :
      ( ( ( k3_xboole_0 @ ( X204 @ X205 ) )
        = X204 )
      | ~ ( r1_tarski @ ( X204 @ X205 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k3_xboole_0 @ ( X0 @ X1 ) ) ) )
      = ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['2','5','6','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
