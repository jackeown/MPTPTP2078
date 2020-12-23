%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0043+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1IoYzPIoOb

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :   81 (  84 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t36_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('1',plain,(
    ! [X146: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X146 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X146: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X146 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( r1_tarski @ ( k4_xboole_0 @ ( C @ B ) @ ( k4_xboole_0 @ ( C @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X158: $i,X159: $i,X160: $i] :
      ( ~ ( r1_tarski @ ( X158 @ X159 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( X160 @ X159 ) @ ( k4_xboole_0 @ ( X160 @ X158 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X1 @ X0 ) @ ( k4_xboole_0 @ ( X1 @ o_0_0_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('6',plain,(
    ! [X165: $i] :
      ( ( k4_xboole_0 @ ( X165 @ k1_xboole_0 ) )
      = X165 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X165: $i] :
      ( ( k4_xboole_0 @ ( X165 @ o_0_0_xboole_0 ) )
      = X165 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
