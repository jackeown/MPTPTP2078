%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0104+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cge4rNdmee

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 22.71s
% Output     : Refutation 22.71s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  171 ( 231 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t97_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
        & ( r1_tarski @ ( k4_xboole_0 @ ( B @ A ) @ C ) ) )
     => ( r1_tarski @ ( k5_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
          & ( r1_tarski @ ( k4_xboole_0 @ ( B @ A ) @ C ) ) )
       => ( r1_tarski @ ( k5_xboole_0 @ ( A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( C @ D ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ ( A @ C ) @ ( k2_xboole_0 @ ( B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X106: $i,X107: $i,X108: $i,X109: $i] :
      ( ~ ( r1_tarski @ ( X106 @ X107 ) )
      | ~ ( r1_tarski @ ( X108 @ X109 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ ( X106 @ X108 ) @ ( k2_xboole_0 @ ( X107 @ X109 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ X1 ) @ ( k2_xboole_0 @ ( sk_C_5 @ X0 ) ) ) )
      | ~ ( r1_tarski @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) @ ( k2_xboole_0 @ ( sk_C_5 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( X0 @ X1 ) @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
