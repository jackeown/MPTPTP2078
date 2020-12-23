%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0082+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DEQaE6LSxw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :  140 ( 159 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)

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

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t75_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X283: $i,X284: $i,X285: $i] :
      ( ~ ( r1_xboole_0 @ ( X283 @ X284 ) )
      | ( r1_xboole_0 @ ( X283 @ ( k3_xboole_0 @ ( X284 @ X285 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( sk_B_2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k3_xboole_0 @ ( X0 @ sk_B_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ ( A @ A ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ A ) )
          & ( A = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X257: $i] :
      ( ( X257 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X257 @ X257 ) ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X257: $i] :
      ( ( X257 = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X257 @ X257 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X37: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( X37 @ X39 ) )
      | ( ( k3_xboole_0 @ ( X37 @ X39 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
