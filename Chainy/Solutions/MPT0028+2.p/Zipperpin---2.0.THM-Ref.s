%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WsaD9CVsGz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 15.68s
% Output     : Refutation 15.68s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  126 ( 135 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t21_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t21_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ) )
 != sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X134: $i,X135: $i] :
      ( r1_tarski @ ( X134 @ ( k2_xboole_0 @ ( X134 @ X135 ) ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) ) )
     => ( r1_tarski @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X110: $i,X111: $i,X112: $i] :
      ( ~ ( r1_tarski @ ( X110 @ X111 ) )
      | ~ ( r1_tarski @ ( X110 @ X112 ) )
      | ( r1_tarski @ ( X110 @ ( k3_xboole_0 @ ( X111 @ X112 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( X0 @ ( k3_xboole_0 @ ( X0 @ X1 ) ) ) )
      | ~ ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( X1 @ ( k3_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('7',plain,(
    ! [X105: $i,X106: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X105 @ X106 ) @ X105 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( X0 @ ( k3_xboole_0 @ ( X0 @ X1 ) ) ) )
      | ( X0
        = ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ ( X1 @ ( k2_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_A_2 != sk_A_2 ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
