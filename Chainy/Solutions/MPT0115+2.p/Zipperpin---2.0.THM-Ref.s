%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0115+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mCSijZo970

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:46 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 121 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t108_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( A @ B ) )
       => ( r1_tarski @ ( k3_xboole_0 @ ( A @ C ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t108_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('1',plain,(
    ! [X145: $i,X146: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X145 @ X146 ) @ X145 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X180: $i,X181: $i] :
      ( ( ( k3_xboole_0 @ ( X180 @ X181 ) )
        = X180 )
      | ~ ( r1_tarski @ ( X180 @ X181 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X147: $i,X148: $i,X149: $i] :
      ( ( r1_tarski @ ( X147 @ X148 ) )
      | ~ ( r1_tarski @ ( X147 @ ( k3_xboole_0 @ ( X148 @ X149 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) )
      | ( r1_tarski @ ( X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( r1_tarski @ ( X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( sk_A_2 @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
