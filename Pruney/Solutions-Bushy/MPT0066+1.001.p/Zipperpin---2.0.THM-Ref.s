%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0066+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yzVFu6ncsr

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   15 (  19 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   55 (  91 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t59_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r2_xboole_0 @ B @ C ) )
       => ( r2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t59_xboole_1])).

thf('0',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X2 )
      | ( r2_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l58_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5'])).


%------------------------------------------------------------------------------
