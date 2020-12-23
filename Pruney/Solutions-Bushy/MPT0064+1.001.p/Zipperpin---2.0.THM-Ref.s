%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0064+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.74MqdL03mn

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   11 (  13 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    4
%              Number of atoms          :   34 (  46 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t57_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ A @ B )
          & ( r2_xboole_0 @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t57_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('2',plain,(
    ~ ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3'])).


%------------------------------------------------------------------------------
