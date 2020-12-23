%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0072+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aN5AKxu2h8

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :   76 (  85 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t65_xboole_1,conjecture,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t65_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ ( A @ k1_xboole_0 ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X154: $i] :
      ( ( k3_xboole_0 @ ( X154 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X154: $i] :
      ( ( k3_xboole_0 @ ( X154 @ o_0_0_xboole_0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( X0 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['2','11'])).

%------------------------------------------------------------------------------
