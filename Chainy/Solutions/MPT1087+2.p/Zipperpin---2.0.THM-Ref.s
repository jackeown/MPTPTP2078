%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1087+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XHiLfbTPv5

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   12 (  14 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_100_type,type,(
    sk_B_100: $i )).

thf(sk_A_17_type,type,(
    sk_A_17: $i )).

thf(fc11_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5689: $i,X5690: $i] :
      ( ~ ( v1_finset_1 @ X5689 )
      | ( v1_finset_1 @ ( k3_xboole_0 @ ( X5689 @ X5690 ) ) ) ) ),
    inference(cnf,[status(esa)],[fc11_finset_1])).

thf(t15_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_finset_1])).

thf('1',plain,(
    ~ ( v1_finset_1 @ ( k3_xboole_0 @ ( sk_A_17 @ sk_B_100 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v1_finset_1 @ sk_A_17 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_finset_1 @ sk_A_17 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    $false ),
    inference(demod,[status(thm)],['2','3'])).

%------------------------------------------------------------------------------
