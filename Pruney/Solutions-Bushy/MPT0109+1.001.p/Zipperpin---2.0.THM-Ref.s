%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0109+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ny8lyTDxl7

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  150 ( 150 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t102_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t102_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('5',plain,(
    ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    $false ),
    inference(simplify,[status(thm)],['5'])).


%------------------------------------------------------------------------------
