%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0069+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BQEmu4fYLf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  31 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   73 (  94 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t62_xboole_1,conjecture,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( r2_xboole_0 @ ( A @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t62_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ ( sk_A_2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    r2_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ ( k1_xboole_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X246: $i] :
      ( ( r2_xboole_0 @ ( k1_xboole_0 @ X246 ) )
      | ( X246 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X246: $i] :
      ( ( r2_xboole_0 @ ( o_0_0_xboole_0 @ X246 ) )
      | ( X246 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r2_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
     => ~ ( r2_xboole_0 @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_xboole_0 @ ( X2 @ X3 ) )
      | ~ ( r2_xboole_0 @ ( X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('9',plain,(
    ~ ( r2_xboole_0 @ ( o_0_0_xboole_0 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A_2 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r2_xboole_0 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['2','10'])).

thf(irreflexivity_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_xboole_0 @ ( A @ A ) ) )).

thf('12',plain,(
    ! [X45: $i] :
      ~ ( r2_xboole_0 @ ( X45 @ X45 ) ) ),
    inference(cnf,[status(esa)],[irreflexivity_r2_xboole_0])).

thf('13',plain,(
    $false ),
    inference('sup-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
