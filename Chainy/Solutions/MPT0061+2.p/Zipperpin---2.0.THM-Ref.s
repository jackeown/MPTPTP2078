%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0061+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ipKV0Cq3TD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    4
%              Number of atoms          :   77 (  77 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t54_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ ( k4_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X88: $i,X89: $i,X90: $i] :
      ( ( k4_xboole_0 @ ( X88 @ ( k3_xboole_0 @ ( X89 @ X90 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X88 @ X89 ) @ ( k4_xboole_0 @ ( X88 @ X90 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
 != ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    $false ),
    inference(simplify,[status(thm)],['2'])).

%------------------------------------------------------------------------------
