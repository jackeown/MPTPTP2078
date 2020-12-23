%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0089+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s5XdM7qCCm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    3
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t82_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('1',plain,(
    ! [X297: $i,X298: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X297 @ X298 ) @ X298 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t80_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X303: $i,X304: $i,X305: $i] :
      ( ~ ( r1_xboole_0 @ ( X303 @ X304 ) )
      | ( r1_xboole_0 @ ( X303 @ ( k4_xboole_0 @ ( X304 @ X305 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t80_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['0','3'])).

%------------------------------------------------------------------------------
