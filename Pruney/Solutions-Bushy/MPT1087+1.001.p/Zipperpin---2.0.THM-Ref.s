%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1087+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t3DyUhK3kA

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:02 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   12 (  14 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc11_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ X0 )
      | ( v1_finset_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc11_finset_1])).

thf(t15_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_finset_1])).

thf('1',plain,(
    ~ ( v1_finset_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3'])).


%------------------------------------------------------------------------------
